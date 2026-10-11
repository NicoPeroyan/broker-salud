"""Gestión de fichas y comisiones para un broker de salud."""

from __future__ import annotations

import csv
import click
import hmac
import io
import logging
import os
import re
import secrets
import sqlite3
import warnings
from contextlib import contextmanager
from datetime import date, datetime
from decimal import Decimal, InvalidOperation
from functools import wraps
from pathlib import Path
from typing import Any, Generator

from flask import (
    Flask,
    Response,
    abort,
    flash,
    make_response,
    redirect,
    render_template,
    request,
    session,
    url_for,
)
from werkzeug.security import check_password_hash, generate_password_hash


BASE_DIR = Path(__file__).resolve().parent
DATABASE_URL = os.environ.get("DATABASE_URL")
DATABASE_PATH = Path(os.environ.get("DATABASE_PATH", BASE_DIR / "app.db"))
PERIOD_RE = re.compile(r"^\d{4}-(0[1-9]|1[0-2])$")
VALID_STATES = {"APROBADA", "RECHAZADA"}
RESET_PASSWORD = "Arper123"

app = Flask(__name__)
secret_key = os.environ.get("FLASK_SECRET_KEY")
if not secret_key:
    secret_key = secrets.token_hex(32)
    warnings.warn(
        "FLASK_SECRET_KEY no está definida; las sesiones se invalidarán al "
        "reiniciar. Defina una clave persistente en producción.",
        RuntimeWarning,
        stacklevel=1,
    )
app.config.update(
    SECRET_KEY=secret_key,
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Lax",
    SESSION_COOKIE_SECURE=os.environ.get("SESSION_COOKIE_SECURE", "").lower()
    in {"1", "true", "yes"},
    MAX_CONTENT_LENGTH=1024 * 1024,
)
logging.basicConfig(level=os.environ.get("LOG_LEVEL", "INFO").upper())
logger = logging.getLogger(__name__)


class DatabaseConnection:
    def __init__(self, raw_connection: Any, is_postgres: bool) -> None:
        self.raw_connection = raw_connection
        self.is_postgres = is_postgres

    def execute(self, statement: str, parameters: Any = ()) -> Any:
        if self.is_postgres:
            statement = statement.replace("?", "%s")
        return self.raw_connection.execute(statement, parameters)

    def commit(self) -> None:
        self.raw_connection.commit()

    def rollback(self) -> None:
        self.raw_connection.rollback()

    def close(self) -> None:
        self.raw_connection.close()


@contextmanager
def db_connection() -> Generator[DatabaseConnection, None, None]:
    """Abre una conexión por operación y garantiza commit/rollback y cierre."""
    if DATABASE_URL:
        import psycopg
        from psycopg.rows import dict_row

        postgres_url = DATABASE_URL
        if postgres_url.startswith("postgres://"):
            postgres_url = "postgresql://" + postgres_url.removeprefix("postgres://")
        elif postgres_url.startswith("postgresql+psycopg://"):
            postgres_url = "postgresql://" + postgres_url.removeprefix(
                "postgresql+psycopg://"
            )
        raw_connection = psycopg.connect(
            postgres_url,
            row_factory=dict_row,
            connect_timeout=15,
        )
        connection = DatabaseConnection(raw_connection, is_postgres=True)
    else:
        DATABASE_PATH.parent.mkdir(parents=True, exist_ok=True)
        raw_connection = sqlite3.connect(DATABASE_PATH, timeout=15)
        raw_connection.row_factory = sqlite3.Row
        connection = DatabaseConnection(raw_connection, is_postgres=False)
    try:
        if not connection.is_postgres:
            connection.execute("PRAGMA foreign_keys = ON")
            connection.execute("PRAGMA busy_timeout = 15000")
        yield connection
        connection.commit()
    except Exception:
        connection.rollback()
        raise
    finally:
        connection.close()


def _columns(connection: DatabaseConnection, table: str) -> set[str]:
    if connection.is_postgres:
        return {
            row["name"]
            for row in connection.execute(
                "SELECT column_name AS name FROM information_schema.columns "
                "WHERE table_schema = current_schema() AND table_name = ?",
                (table,),
            )
        }
    return {row["name"] for row in connection.execute(f"PRAGMA table_info({table})")}


def _table_exists(connection: DatabaseConnection, table: str) -> bool:
    if connection.is_postgres:
        query = (
            "SELECT 1 FROM information_schema.tables "
            "WHERE table_schema = current_schema() AND table_name = ?"
        )
    else:
        query = "SELECT 1 FROM sqlite_master WHERE type = 'table' AND name = ?"
    return connection.execute(query, (table,)).fetchone() is not None


def _add_column(
    connection: DatabaseConnection, table: str, name: str, declaration: str
) -> None:
    if name not in _columns(connection, table):
        connection.execute(f"ALTER TABLE {table} ADD COLUMN {name} {declaration}")


def init_db() -> None:
    """Crea las tablas nuevas y migra de forma aditiva las instalaciones previas."""
    with db_connection() as connection:
        user_id_type = "SERIAL PRIMARY KEY" if connection.is_postgres else (
            "INTEGER PRIMARY KEY AUTOINCREMENT"
        )
        ficha_id_type = user_id_type
        connection.execute(
            f"""
            CREATE TABLE IF NOT EXISTS usuarios (
                id {user_id_type},
                username TEXT NOT NULL UNIQUE,
                password TEXT NOT NULL DEFAULT '',
                rol TEXT NOT NULL DEFAULT 'asesor'
                    CHECK (rol IN ('admin', 'asesor')),
                nombre_completo TEXT NOT NULL DEFAULT '',
                email TEXT UNIQUE,
                password_hash TEXT,
                nombre TEXT,
                es_admin BOOLEAN DEFAULT FALSE,
                fecha_creacion TEXT DEFAULT CURRENT_TIMESTAMP
            )
            """
        )
        connection.execute(
            f"""
            CREATE TABLE IF NOT EXISTS fichas (
                id {ficha_id_type},
                asesor_id INTEGER NOT NULL,
                cliente_nombre TEXT,
                cuil TEXT,
                prepaga TEXT NOT NULL,
                plan TEXT,
                importe_comision REAL NOT NULL DEFAULT 0,
                estado TEXT NOT NULL DEFAULT 'PENDIENTE'
                    CHECK (estado IN ('PENDIENTE', 'APROBADA', 'RECHAZADA')),
                periodo TEXT,
                fecha_carga TEXT,
                nombre_afiliado TEXT,
                cuil_afiliado TEXT,
                grupo_familiar TEXT NOT NULL DEFAULT 'Sin especificar',
                sueldo_bruto REAL DEFAULT 0,
                aporte REAL DEFAULT 0,
                porcentaje_comision REAL DEFAULT 1,
                motivo_rechazo TEXT,
                fecha_creacion TEXT DEFAULT CURRENT_TIMESTAMP,
                FOREIGN KEY (asesor_id) REFERENCES usuarios(id)
            )
            """
        )

        for name, declaration in (
            ("username", "TEXT"),
            ("password", "TEXT"),
            ("rol", "TEXT NOT NULL DEFAULT 'asesor'"),
            ("nombre_completo", "TEXT"),
            ("email", "TEXT"),
            ("password_hash", "TEXT"),
            ("nombre", "TEXT"),
            ("es_admin", "BOOLEAN DEFAULT FALSE"),
            ("fecha_creacion", "TEXT"),
        ):
            _add_column(connection, "usuarios", name, declaration)

        ficha_columns_before_migration = _columns(connection, "fichas")
        ficha_columns = (
            ("cliente_nombre", "TEXT"),
            ("cuil", "TEXT"),
            ("prepaga", "TEXT"),
            ("plan", "TEXT"),
            ("importe_comision", "REAL NOT NULL DEFAULT 0"),
            ("estado", "TEXT NOT NULL DEFAULT 'PENDIENTE'"),
            ("periodo", "TEXT"),
            ("fecha_carga", "TEXT"),
            ("nombre_afiliado", "TEXT"),
            ("cuil_afiliado", "TEXT"),
            ("grupo_familiar", "TEXT NOT NULL DEFAULT 'Sin especificar'"),
            ("sueldo_bruto", "REAL DEFAULT 0"),
            ("aporte", "REAL DEFAULT 0"),
            ("porcentaje_comision", "REAL DEFAULT 1"),
            ("motivo_rechazo", "TEXT"),
            ("fecha_creacion", "TEXT"),
        )
        for name, declaration in ficha_columns:
            _add_column(connection, "fichas", name, declaration)

        if connection.is_postgres:
            connection.execute(
                "ALTER TABLE fichas ALTER COLUMN grupo_familiar TYPE TEXT "
                "USING grupo_familiar::TEXT"
            )
            connection.execute(
                "ALTER TABLE fichas ALTER COLUMN grupo_familiar "
                "SET DEFAULT 'Sin especificar'"
            )
            connection.execute(
                "UPDATE fichas SET grupo_familiar = 'Sin especificar' "
                "WHERE grupo_familiar IS NULL"
            )
            connection.execute(
                "ALTER TABLE fichas ALTER COLUMN grupo_familiar SET NOT NULL"
            )
        else:
            connection.execute(
                "UPDATE fichas SET grupo_familiar = 'Sin especificar' "
                "WHERE grupo_familiar IS NULL"
            )

        connection.execute(
            """
            UPDATE usuarios
            SET username = COALESCE(NULLIF(username, ''), email, 'usuario-' || id),
                password = COALESCE(NULLIF(password, ''), password_hash, ''),
                nombre_completo = COALESCE(
                    NULLIF(nombre_completo, ''), NULLIF(nombre, ''), username
                ),
                rol = CASE
                    WHEN LOWER(COALESCE(rol, '')) = 'admin'
                         OR es_admin IS TRUE THEN 'admin'
                    ELSE 'asesor'
                END
            """
        )

        if "importe_comision" not in ficha_columns_before_migration:
            commission_expression = (
                "COALESCE(aporte, 0) * COALESCE(porcentaje_comision, 1)"
            )
            connection.execute(
                f"UPDATE fichas SET importe_comision = {commission_expression}"
            )

        fecha_carga_fallback = (
            "CURRENT_DATE::TEXT"
            if connection.is_postgres
            else "date('now', 'localtime')"
        )
        periodo_fallback = (
            "TO_CHAR(CURRENT_DATE, 'YYYY-MM')"
            if connection.is_postgres
            else "strftime('%Y-%m', 'now', 'localtime')"
        )
        connection.execute(
            f"""
            UPDATE fichas
            SET cliente_nombre = COALESCE(
                    NULLIF(cliente_nombre, ''), nombre_afiliado, ''
                ),
                cuil = COALESCE(NULLIF(cuil, ''), cuil_afiliado, ''),
                fecha_carga = COALESCE(
                    NULLIF(fecha_carga, ''), substr(fecha_creacion, 1, 10),
                    {fecha_carga_fallback}
                ),
                periodo = COALESCE(
                    NULLIF(periodo, ''), substr(fecha_creacion, 1, 7),
                    {periodo_fallback}
                ),
                estado = CASE UPPER(TRIM(COALESCE(estado, '')))
                    WHEN 'APROBADA' THEN 'APROBADA'
                    WHEN 'APROBADO' THEN 'APROBADA'
                    WHEN 'RECHAZADA' THEN 'RECHAZADA'
                    WHEN 'RECHAZADO' THEN 'RECHAZADA'
                    ELSE 'PENDIENTE'
                END
            """
        )
        connection.execute(
            "CREATE UNIQUE INDEX IF NOT EXISTS idx_usuarios_username "
            "ON usuarios(username)"
        )
        connection.execute(
            "CREATE INDEX IF NOT EXISTS idx_fichas_periodo_asesor "
            "ON fichas(periodo, asesor_id)"
        )
        connection.execute(
            "CREATE INDEX IF NOT EXISTS idx_fichas_estado_prepaga "
            "ON fichas(estado, prepaga)"
        )
        connection.execute(
            """
            CREATE TABLE IF NOT EXISTS cierres_periodo (
                periodo TEXT PRIMARY KEY,
                fecha_cierre TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
                cerrado_por INTEGER,
                FOREIGN KEY (cerrado_por) REFERENCES usuarios(id)
            )
            """
        )
        connection.execute(
            """
            CREATE TABLE IF NOT EXISTS cierres_prepaga (
                periodo TEXT NOT NULL,
                prepaga TEXT NOT NULL,
                fecha_cierre TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
                cerrado_por INTEGER,
                PRIMARY KEY (periodo, prepaga),
                FOREIGN KEY (cerrado_por) REFERENCES usuarios(id)
            )
            """
        )


def _month_after(period: str) -> str:
    year, month = map(int, period.split("-"))
    return f"{year + (month == 12):04d}-{1 if month == 12 else month + 1:02d}"


def _active_period(
    connection: DatabaseConnection, prepaga: str | None = None
) -> str:
    current_period = date.today().strftime("%Y-%m")
    if prepaga is None:
        last_closed = connection.execute(
            "SELECT MAX(periodo) AS periodo FROM cierres_periodo"
        ).fetchone()["periodo"]
    else:
        last_closed = connection.execute(
            """
            SELECT MAX(periodo) AS periodo FROM (
                SELECT periodo FROM cierres_periodo
                UNION ALL
                SELECT periodo FROM cierres_prepaga WHERE prepaga = ?
            )
            """,
            (prepaga,),
        ).fetchone()["periodo"]
    if last_closed and last_closed >= current_period:
        return max(current_period, _month_after(last_closed))
    return current_period


def _filter_active_prepaga_periods(
    connection: DatabaseConnection,
    clauses: list[str],
    values: list[Any],
    prepaga_filter: str,
) -> tuple[list[str], list[Any]]:
    prepagas = (
        [prepaga_filter]
        if prepaga_filter
        else [
            row["prepaga"]
            for row in connection.execute(
                "SELECT DISTINCT prepaga FROM fichas "
                "WHERE prepaga IS NOT NULL AND prepaga != '' "
                "ORDER BY LOWER(prepaga)"
            )
        ]
    )
    if not prepagas:
        return [*clauses, "1 = 0"], values.copy()

    active_clauses = [
        "(f.prepaga = ? AND f.periodo = ?)" for _ in prepagas
    ]
    active_values: list[Any] = []
    for prepaga in prepagas:
        active_values.extend((prepaga, _active_period(connection, prepaga)))
    return [*clauses, "(" + " OR ".join(active_clauses) + ")"], [
        *values,
        *active_values,
    ]


def format_ars(value: Any, decimals: int = 0) -> str:
    """Formatea importes con separador de miles '.' y decimal ','."""
    try:
        amount = Decimal(str(value or 0))
    except (InvalidOperation, ValueError, TypeError):
        amount = Decimal(0)
    rendered = f"{amount:,.{decimals}f}"
    return "$ " + rendered.replace(",", "_").replace(".", ",").replace("_", ".")


app.jinja_env.filters["ars"] = format_ars


def _dict_ficha(row: Any) -> dict[str, Any]:
    ficha = dict(row)
    ficha["estado"] = str(ficha.get("estado") or "PENDIENTE").upper()
    ficha["nombre_afiliado"] = ficha.get("cliente_nombre") or ""
    ficha["cuil_afiliado"] = ficha.get("cuil") or ""
    ficha["monto_comision"] = ficha.get("importe_comision") or 0
    ficha["comision_a_liquidar"] = (
        ficha["monto_comision"] if ficha["estado"] == "APROBADA" else 0
    )
    ficha["aporte"] = ficha.get("aporte") or 0
    ficha["porcentaje_comision"] = ficha.get("porcentaje_comision") or 0
    ficha["fecha_creacion"] = ficha.get("fecha_carga") or ""
    ficha["asesor_nombre"] = ficha.get("nombre_completo") or "Asesor"
    return ficha


def _dashboard_filters() -> tuple[list[str], list[Any], str, str, str, str | None]:
    clauses: list[str] = []
    values: list[Any] = []

    raw_advisor = request.args.get("asesor_id", "todos").strip()
    advisor_id: str | None = None
    if raw_advisor.lower() not in {"", "todos"}:
        if not raw_advisor.isdecimal() or int(raw_advisor) < 1:
            abort(400, description="El asesor seleccionado no es válido.")
        advisor_id = str(int(raw_advisor))
        clauses.append("f.asesor_id = ?")
        values.append(int(advisor_id))

    period = request.args.get("periodo", "").strip()
    if not period:
        period = request.args.get("period", "").strip()
    if not period:
        month = request.args.get("mes", "").strip()
        year = request.args.get("año", request.args.get("anio", "")).strip()
        if month and year:
            try:
                period = f"{int(year):04d}-{int(month):02d}"
            except ValueError:
                abort(400, description="El período seleccionado no es válido.")
    if not period:
        period = "activo"
    if period.lower() not in {"todos", "todo"}:
        if period.lower() == "activo":
            period = "activo"
        elif not PERIOD_RE.fullmatch(period):
            abort(400, description="El período debe tener formato AAAA-MM.")
        else:
            clauses.append("f.periodo = ?")
            values.append(period)

    prepaga = request.args.get("prepaga", "").strip()
    if prepaga:
        clauses.append("f.prepaga = ?")
        values.append(prepaga)

    query = request.args.get("q", "").strip()
    if len(query) > 100:
        abort(400, description="La búsqueda no puede superar los 100 caracteres.")
    if query:
        escaped_query = query.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_")
        clauses.append(
            "(f.cliente_nombre LIKE ? ESCAPE '\\' "
            "OR f.cuil LIKE ? ESCAPE '\\')"
        )
        search = f"%{escaped_query}%"
        values.extend((search, search))

    return clauses, values, period, prepaga, query, advisor_id


def _query_filters(
    clauses: list[str], values: list[Any], prefix: str = "WHERE"
) -> tuple[str, list[Any]]:
    if not clauses:
        return "", []
    return f" {prefix} " + " AND ".join(clauses), values


def admin_required(view: Any) -> Any:
    @wraps(view)
    def wrapped(*args: Any, **kwargs: Any) -> Any:
        if "user_id" not in session:
            return redirect(url_for("login", next=request.full_path.rstrip("?")))
        if session.get("rol") != "admin":
            abort(403)
        return view(*args, **kwargs)

    return wrapped


def login_required(view: Any) -> Any:
    @wraps(view)
    def wrapped(*args: Any, **kwargs: Any) -> Any:
        if "user_id" not in session:
            return redirect(url_for("login", next=request.full_path.rstrip("?")))
        return view(*args, **kwargs)

    return wrapped


def _password_matches(stored_password: str, supplied_password: str) -> bool:
    if not stored_password:
        return False
    try:
        if check_password_hash(stored_password, supplied_password):
            return True
    except (ValueError, TypeError):
        pass
    return hmac.compare_digest(stored_password, supplied_password)


@app.get("/")
def index() -> Any:
    if session.get("rol") == "admin":
        return redirect(url_for("admin_dashboard"))
    if session.get("rol") == "asesor":
        return redirect(url_for("mis_fichas"))
    return redirect(url_for("login"))


@app.route("/login", methods=["GET", "POST"])
def login() -> Any:
    if request.method == "GET":
        if session.get("rol") == "admin":
            return redirect(url_for("admin_dashboard"))
        return render_template("login.html", error=None)

    identity = (request.form.get("email") or request.form.get("username") or "").strip()
    password = request.form.get("password", "")
    with db_connection() as connection:
        user = connection.execute(
            """
            SELECT id, username, password, rol, nombre_completo
            FROM usuarios
            WHERE LOWER(username) = LOWER(?) OR LOWER(COALESCE(email, '')) = LOWER(?)
            LIMIT 1
            """,
            (identity, identity),
        ).fetchone()
    if user is None or not _password_matches(user["password"] or "", password):
        return render_template("login.html", error="Usuario o contraseña incorrectos."), 401

    session.clear()
    session["user_id"] = user["id"]
    session["username"] = user["username"]
    session["nombre"] = user["nombre_completo"] or user["username"]
    session["rol"] = user["rol"]
    if user["rol"] == "admin":
        return redirect(url_for("admin_dashboard"))
    return redirect(url_for("mis_fichas"))


@app.get("/logout")
def logout() -> Any:
    session.clear()
    return redirect(url_for("login"))


@app.get("/admin-dashboard")
@admin_required
def admin_dashboard() -> Any:
    clauses, values, period, prepaga, query, selected_advisor_id = _dashboard_filters()
    with db_connection() as connection:
        advisors = [
            dict(row)
            for row in connection.execute(
                """
                SELECT id, username, nombre_completo
                FROM usuarios WHERE rol = 'asesor'
                ORDER BY LOWER(nombre_completo), id
                """
            )
        ]
        prepaga_options = [
            row["prepaga"]
            for row in connection.execute(
                "SELECT DISTINCT prepaga FROM fichas "
                "WHERE prepaga IS NOT NULL AND prepaga != '' "
                "ORDER BY LOWER(prepaga)"
            )
        ]
        selected_advisor = next(
            (advisor for advisor in advisors if str(advisor["id"]) == selected_advisor_id),
            None,
        )
        # An unknown but syntactically valid adviser must not broaden the result set.
        if selected_advisor_id and selected_advisor is None:
            clauses = [*clauses, "1 = 0"]
        effective_clauses = clauses
        effective_values = values
        if period == "activo":
            effective_clauses, effective_values = _filter_active_prepaga_periods(
                connection, clauses, values, prepaga
            )
        where_clause, query_values = _query_filters(
            effective_clauses, effective_values
        )
        rows = connection.execute(
            f"""
            SELECT f.*, u.nombre_completo
            FROM fichas AS f
            LEFT JOIN usuarios AS u ON u.id = f.asesor_id
            {where_clause}
            ORDER BY f.fecha_carga DESC, f.id DESC
            """,
            query_values,
        ).fetchall()
        summary_clauses = clauses.copy()
        summary_values = values.copy()
        if period == "activo":
            summary_clauses, summary_values = _filter_active_prepaga_periods(
                connection, summary_clauses, summary_values, prepaga
            )
        summary_where, summary_query_values = _query_filters(
            summary_clauses, summary_values
        )
        summary_rows = connection.execute(
            f"""
            SELECT f.prepaga,
                   SUM(CASE WHEN f.estado = 'APROBADA'
                            THEN COALESCE(f.importe_comision, 0) ELSE 0 END) AS total
            FROM fichas AS f
            {summary_where}
            GROUP BY f.prepaga
            ORDER BY LOWER(f.prepaga)
            """,
            summary_query_values,
        ).fetchall()
        period_rows = connection.execute(
            """
            SELECT periodo FROM fichas WHERE periodo IS NOT NULL
            UNION
            SELECT periodo FROM cierres_periodo
            UNION
            SELECT periodo FROM cierres_prepaga
            ORDER BY periodo DESC
            """
        ).fetchall()
        active_periods = {
            brand: _active_period(connection, brand) for brand in prepaga_options
        }
        active_period = _active_period(connection)
        period_options = sorted(
            {row["periodo"] for row in period_rows if row["periodo"]}
            | set(active_periods.values())
            | {active_period},
            reverse=True,
        )

    fichas = [_dict_ficha(row) for row in rows]
    totales_prepaga = {brand: 0 for brand in prepaga_options}
    for row in summary_rows:
        totales_prepaga[row["prepaga"] or "Sin prepaga"] = row["total"] or 0
    total_general = sum(totales_prepaga.values())
    return render_template(
        "admin_dashboard.html",
        fichas=fichas,
        asesores=advisors,
        prepagas=prepaga_options,
        periodos_prepaga=active_periods,
        totales_prepaga=totales_prepaga,
        prepaga_totals=totales_prepaga,
        total_general=total_general,
        asesor_seleccionado=selected_advisor,
        asesor_id_actual=selected_advisor_id or "todos",
        periodos=period_options,
        periodo_actual=period,
        periodo_operativo=active_period,
        periodos_operativos=active_periods,
        prepaga_actual=prepaga,
        q_actual=query,
        mes=int(period[5:]) if PERIOD_RE.fullmatch(period) else "",
        año=int(period[:4]) if PERIOD_RE.fullmatch(period) else "",
        es_admin=True,
        nombre=session.get("nombre", ""),
        route="admin",
    )


@app.get("/admin")
def admin_legacy() -> Any:
    return redirect(url_for("admin_dashboard"))


def _change_ficha_state(ficha_id: int, state: str) -> Any:
    with db_connection() as connection:
        ficha = connection.execute(
            "SELECT periodo, prepaga FROM fichas WHERE id = ?", (ficha_id,)
        ).fetchone()
        if ficha is None:
            abort(404)
        closed = connection.execute(
            """
            SELECT 1 FROM cierres_periodo WHERE periodo = ?
            UNION ALL
            SELECT 1 FROM cierres_prepaga WHERE periodo = ? AND prepaga = ?
            LIMIT 1
            """,
            (ficha["periodo"], ficha["periodo"], ficha["prepaga"]),
        ).fetchone()
        if closed:
            flash("No se puede modificar una ficha de un período cerrado.")
        else:
            connection.execute(
                "UPDATE fichas SET estado = ? WHERE id = ?", (state, ficha_id)
            )
            flash(f"Ficha {state.lower()} correctamente.")
    return redirect(url_for("admin_dashboard", **request.args.to_dict()))


@app.post("/cambiar-estado-ficha/<int:ficha_id>")
@admin_required
def cambiar_estado_ficha(ficha_id: int) -> Any:
    state = request.form.get("estado", "").strip().upper()
    if state not in VALID_STATES:
        abort(400, description="El estado debe ser APROBADA o RECHAZADA.")
    return _change_ficha_state(ficha_id, state)


@app.post("/fichas/<int:ficha_id>/aprobar")
@admin_required
def aprobar_ficha_legacy(ficha_id: int) -> Any:
    return _change_ficha_state(ficha_id, "APROBADA")


@app.post("/fichas/<int:ficha_id>/rechazar")
@admin_required
def rechazar_ficha_legacy(ficha_id: int) -> Any:
    return _change_ficha_state(ficha_id, "RECHAZADA")


@app.post("/cerrar-periodo")
@admin_required
def cerrar_periodo() -> Any:
    with db_connection() as connection:
        requested_prepaga = request.form.get("prepaga", "").strip()
        requested_period = request.form.get("periodo", "").strip()
        if requested_prepaga:
            if not requested_period or not PERIOD_RE.fullmatch(requested_period):
                abort(400, description="El período a cerrar no es válido.")
            active_period = _active_period(connection, requested_prepaga)
            if requested_period != active_period:
                abort(400, description="Solo se puede cerrar el período activo de esa prepaga.")
            existing = connection.execute(
                "SELECT 1 FROM cierres_prepaga WHERE periodo = ? AND prepaga = ?",
                (requested_period, requested_prepaga),
            ).fetchone()
            if existing:
                abort(409, description="El período de esa prepaga ya está cerrado.")
            connection.execute(
                """
                INSERT INTO cierres_prepaga (periodo, prepaga, cerrado_por)
                VALUES (?, ?, ?)
                """,
                (requested_period, requested_prepaga, session["user_id"]),
            )
            next_period = _month_after(requested_period)
            flash(
                f"Período {requested_period} de {requested_prepaga} cerrado. "
                f"El nuevo período activo para esa prepaga es {next_period}."
            )
            redirect_args = {
                "periodo": "activo",
                "asesor_id": request.form.get("asesor_id", "todos"),
                "prepaga": request.form.get("filtro_prepaga", ""),
                "q": request.form.get("q", ""),
            }
            return redirect(url_for("admin_dashboard", **redirect_args))

        active_period = _active_period(connection)
        requested_period = requested_period or active_period
        if not PERIOD_RE.fullmatch(requested_period):
            abort(400, description="El período a cerrar no es válido.")
        if requested_period != active_period:
            abort(400, description="Solo se puede cerrar el período activo.")
        brands = [
            row["prepaga"]
            for row in connection.execute(
                "SELECT DISTINCT prepaga FROM fichas "
                "WHERE prepaga IS NOT NULL AND prepaga != ''"
            )
        ]
        for brand in brands:
            brand_period = _active_period(connection, brand)
            if connection.execute(
                "SELECT 1 FROM cierres_prepaga WHERE periodo = ? AND prepaga = ?",
                (brand_period, brand),
            ).fetchone():
                continue
            connection.execute(
                """
                INSERT INTO cierres_prepaga (periodo, prepaga, cerrado_por)
                VALUES (?, ?, ?)
                """,
                (brand_period, brand, session["user_id"]),
            )
        if not brands:
            connection.execute(
                """
                INSERT OR IGNORE INTO cierres_periodo (periodo, cerrado_por)
                VALUES (?, ?)
                """,
                (requested_period, session["user_id"]),
            )
        flash("Período activo cerrado para todas las prepagas.")
    return redirect(url_for("admin_dashboard", periodo="activo"))


def _selected_fichas_for_export() -> list[dict[str, Any]]:
    clauses, values, period, prepaga, _, selected_advisor_id = _dashboard_filters()
    with db_connection() as connection:
        if selected_advisor_id:
            advisor = connection.execute(
                "SELECT 1 FROM usuarios WHERE id = ? AND rol = 'asesor'",
                (int(selected_advisor_id),),
            ).fetchone()
            if advisor is None:
                clauses = [*clauses, "1 = 0"]
        if period == "activo":
            clauses, values = _filter_active_prepaga_periods(
                connection, clauses, values, prepaga
            )
        where_clause, query_values = _query_filters(clauses, values)
        rows = connection.execute(
            f"""
            SELECT f.*, u.nombre_completo
            FROM fichas AS f
            LEFT JOIN usuarios AS u ON u.id = f.asesor_id
            {where_clause}
            ORDER BY f.fecha_carga DESC, f.id DESC
            """,
            query_values,
        ).fetchall()
    return [_dict_ficha(row) for row in rows]


@app.get("/exportar-excel")
@admin_required
def exportar_excel() -> Response:
    fichas = _selected_fichas_for_export()
    output = io.StringIO(newline="")
    writer = csv.writer(output)
    writer.writerow(
        [
            "ID",
            "Período",
            "Fecha de carga",
            "Asesor",
            "Cliente",
            "CUIL",
            "Prepaga",
            "Plan",
            "Estado",
            "Comisión registrada",
            "Comisión a liquidar",
        ]
    )
    for ficha in fichas:
        amount = Decimal(str(ficha["importe_comision"] or 0))
        payable = amount if ficha["estado"] == "APROBADA" else Decimal(0)
        writer.writerow(
            [
                ficha["id"],
                ficha["periodo"],
                ficha["fecha_carga"],
                ficha["asesor_nombre"],
                ficha["cliente_nombre"],
                ficha["cuil"],
                ficha["prepaga"],
                ficha["plan"] or "",
                ficha["estado"],
                f"{amount:.2f}",
                f"{payable:.2f}",
            ]
        )
    response = make_response("\ufeff" + output.getvalue())
    response.headers["Content-Type"] = "text/csv; charset=utf-8"
    response.headers["Content-Disposition"] = (
        'attachment; filename="reporte_comisiones.csv"'
    )
    return response


def _advisor_dashboard_data(
    advisor_id: int,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], Decimal]:
    with db_connection() as connection:
        brands = [
            row["prepaga"]
            for row in connection.execute(
                """
                SELECT DISTINCT prepaga
                FROM fichas
                WHERE asesor_id = ? AND prepaga IS NOT NULL AND prepaga != ''
                ORDER BY LOWER(prepaga)
                """,
                (advisor_id,),
            )
        ]
        summaries: list[dict[str, Any]] = []
        grand_total = Decimal(0)
        for brand in brands:
            active_period = _active_period(connection, brand)
            totals = connection.execute(
                """
                SELECT COUNT(*) AS fichas_total,
                       SUM(CASE WHEN estado = 'APROBADA' THEN 1 ELSE 0 END)
                           AS fichas_aprobadas,
                       SUM(CASE WHEN estado = 'APROBADA'
                                THEN COALESCE(importe_comision, 0) ELSE 0 END)
                           AS importe_a_liquidar
                FROM fichas
                WHERE asesor_id = ? AND prepaga = ? AND periodo = ?
                """,
                (advisor_id, brand, active_period),
            ).fetchone()
            amount = Decimal(str(totals["importe_a_liquidar"] or 0))
            grand_total += amount
            summaries.append(
                {
                    "prepaga": brand,
                    "periodo": active_period,
                    "fichas_total": totals["fichas_total"] or 0,
                    "fichas_aprobadas": totals["fichas_aprobadas"] or 0,
                    "importe_a_liquidar": amount,
                    "importe_formateado": format_ars(amount),
                }
            )
        fichas = connection.execute(
            """
            SELECT f.*, u.nombre_completo
            FROM fichas AS f
            LEFT JOIN usuarios AS u ON u.id = f.asesor_id
            WHERE f.asesor_id = ?
            ORDER BY f.fecha_carga DESC, f.id DESC
            """,
            (advisor_id,),
        ).fetchall()
    return [_dict_ficha(row) for row in fichas], summaries, grand_total


@app.get("/mis-fichas")
@login_required
def mis_fichas() -> Any:
    if session.get("rol") != "asesor":
        abort(403)
    fichas, summaries, grand_total = _advisor_dashboard_data(int(session["user_id"]))
    return render_template(
        "mis_fichas.html",
        fichas=fichas,
        resumen_prepagas=summaries,
        total_general=grand_total,
        total_general_formateado=format_ars(grand_total),
        periodo_actual=date.today().strftime("%Y-%m"),
        nombre=session.get("nombre", ""),
        es_admin=False,
        route="mis-fichas",
    )


@app.get("/asesor-dashboard")
@login_required
def asesor_dashboard_page() -> Any:
    if session.get("rol") != "asesor":
        abort(403)
    fichas, summaries, grand_total = _advisor_dashboard_data(int(session["user_id"]))
    return render_template(
        "asesor_dashboard.html",
        fichas=fichas[:5],
        resumen_prepagas=summaries,
        total_general=grand_total,
        total_general_formateado=format_ars(grand_total),
        periodo_actual=date.today().strftime("%Y-%m"),
        nombre=session.get("nombre", ""),
        es_admin=False,
        route="dashboard",
    )


@app.get("/asesor")
@login_required
def asesor_dashboard() -> Any:
    return redirect(url_for("asesor_dashboard_page"))


@app.get("/cargar-ficha")
@login_required
def cargar_ficha() -> Any:
    if session.get("rol") != "asesor":
        abort(403)
    return render_template(
        "cargar_ficha.html",
        nombre=session.get("nombre", ""),
        es_admin=False,
        route="cargar-ficha",
        csrf_token=lambda: "",
    )


def _parse_amount(raw_value: str) -> Decimal:
    cleaned = raw_value.strip().replace("$", "").replace(" ", "")
    if "," in cleaned:
        cleaned = cleaned.replace(".", "").replace(",", ".")
    try:
        amount = Decimal(cleaned)
    except InvalidOperation as exc:
        raise ValueError("El importe de comisión no es válido.") from exc
    if not amount.is_finite() or amount < 0:
        raise ValueError("El importe de comisión debe ser un valor no negativo.")
    return amount


@app.post("/fichas")
@login_required
def crear_ficha() -> Any:
    if session.get("rol") != "asesor":
        abort(403)
    client_name = (
        request.form.get("cliente_nombre") or request.form.get("nombre_afiliado") or ""
    ).strip()
    cuil = (request.form.get("cuil") or request.form.get("cuil_afiliado") or "").strip()
    prepaga = request.form.get("prepaga", "").strip()
    plan = request.form.get("plan", "").strip()
    grupo_familiar = request.form.get("grupo_familiar") or "Sin especificar"
    raw_commission = request.form.get("importe_comision", "").strip()
    try:
        if not client_name or not cuil or not prepaga:
            raise ValueError("Nombre, CUIL y prepaga son obligatorios.")
        commission = _parse_amount(
            raw_commission or request.form.get("aporte", "0")
        )
        active_period = date.today().strftime("%Y-%m")
        with db_connection() as connection:
            active_period = _active_period(connection)
            connection.execute(
                """
                INSERT INTO fichas (
                    asesor_id, cliente_nombre, cuil, prepaga, plan,
                    importe_comision, estado, periodo, fecha_carga,
                    nombre_afiliado, cuil_afiliado, grupo_familiar, aporte,
                    fecha_creacion
                ) VALUES (?, ?, ?, ?, ?, ?, 'PENDIENTE', ?, ?, ?, ?, ?, ?, ?)
                """,
                (
                    session["user_id"],
                    client_name,
                    cuil,
                    prepaga,
                    plan,
                    float(commission),
                    active_period,
                    date.today().isoformat(),
                    client_name,
                    cuil,
                    grupo_familiar,
                    float(commission),
                    datetime.now().isoformat(timespec="seconds"),
                ),
            )
        flash("Ficha cargada correctamente.")
        return redirect(url_for("mis_fichas"))
    except ValueError as exc:
        flash(str(exc))
        return redirect(url_for("cargar_ficha"))


@app.cli.command("limpiar-db-pruebas")
@click.option(
    "--confirmar",
    is_flag=True,
    help="Confirma el borrado de fichas y el restablecimiento de todas las claves.",
)
def limpiar_db_pruebas(confirmar: bool) -> None:
    """Limpia datos de prueba y restablece las cuentas a la clave temporal configurada."""
    if not confirmar:
        raise click.ClickException(
            "Operación cancelada. Vuelve a ejecutar con --confirmar para "
            "borrar las fichas y restablecer la contraseña temporal de todos."
        )

    with db_connection() as connection:
        user_columns = _columns(connection, "usuarios")
        users = connection.execute("SELECT id FROM usuarios ORDER BY id").fetchall()
        for user in users:
            password_hash = generate_password_hash(RESET_PASSWORD)
            assignments = ["password = ?"]
            parameters: list[Any] = [password_hash]
            if "password_hash" in user_columns:
                assignments.append("password_hash = ?")
                parameters.append(password_hash)
            parameters.append(user["id"])
            connection.execute(
                f"UPDATE usuarios SET {', '.join(assignments)} WHERE id = ?",
                parameters,
            )

        fichas_deleted = connection.execute("DELETE FROM fichas").rowcount
        cierres_prepaga_deleted = 0
        cierres_periodo_deleted = 0
        if _table_exists(connection, "cierres_prepaga"):
            cierres_prepaga_deleted = connection.execute(
                "DELETE FROM cierres_prepaga"
            ).rowcount
        if _table_exists(connection, "cierres_periodo"):
            cierres_periodo_deleted = connection.execute(
                "DELETE FROM cierres_periodo"
            ).rowcount

    click.echo(f"Fichas eliminadas: {max(fichas_deleted, 0)}")
    click.echo(
        "Cierres de prepaga/globales eliminados: "
        f"{max(cierres_prepaga_deleted, 0)}/{max(cierres_periodo_deleted, 0)}"
    )
    click.echo(
        f"Contraseñas restablecidas: {len(users)}. "
        "Clave temporal común restablecida correctamente."
    )
    click.echo("Nombres, usernames y roles de los usuarios se conservaron.")


# Importing the WSGI application also guarantees the database schema is ready.
init_db()


if __name__ == "__main__":
    app.run(
        host=os.environ.get("FLASK_HOST", "127.0.0.1"),
        port=int(os.environ.get("FLASK_PORT", "5000")),
        debug=os.environ.get("FLASK_DEBUG", "").lower() in {"1", "true", "yes"},
    )