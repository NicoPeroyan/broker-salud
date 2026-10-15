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
from datetime import date, datetime, timedelta
from decimal import Decimal, InvalidOperation
from functools import wraps
from pathlib import Path
from typing import Any, Generator

from flask import (
    Flask,
    Response,
    abort,
    flash,
    has_request_context,
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
PASSWORD_HASH_RE = re.compile(
    r"^(?:scrypt:\d+:\d+:\d+|pbkdf2:[^$]+)\$[^$]+\$[^$]+$"
)
VALID_STATES = {"APROBADA", "RECHAZADA"}
DEFAULT_PREPAGAS = ("Premedic", "Andes Salud", "Prevención Salud", "Nobis")

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
    SESSION_COOKIE_SECURE=True,
    MAX_CONTENT_LENGTH=1024 * 1024,
)
logging.basicConfig(level=os.environ.get("LOG_LEVEL", "INFO").upper())
logger = logging.getLogger(__name__)


def csrf_token() -> str:
    token = session.get("_csrf_token")
    if not isinstance(token, str):
        token = secrets.token_urlsafe(32)
        session["_csrf_token"] = token
    return token


@app.context_processor
def inject_csrf_token() -> dict[str, Any]:
    return {"csrf_token": csrf_token}


@app.before_request
def validate_csrf_token() -> None:
    if request.method not in {"POST", "PUT", "PATCH", "DELETE"}:
        return

    expected_token = session.get("_csrf_token")
    submitted_token = request.form.get("csrf_token", "")
    if (
        not isinstance(expected_token, str)
        or not submitted_token
        or not hmac.compare_digest(expected_token, submitted_token)
    ):
        abort(400, description="Token CSRF ausente o inválido.")


@app.before_request
def enforce_active_agency_session() -> Any | None:
    user_id = session.get("user_id")
    if user_id is None:
        return None
    with db_connection() as connection:
        user = connection.execute(
            """
            SELECT u.rol, u.es_superadmin, u.agencia_id, a.estado
            FROM usuarios AS u
            LEFT JOIN agencias AS a ON a.id = u.agencia_id
            WHERE u.id = ?
            """,
            (user_id,),
        ).fetchone()
    if user is not None and (
        user["rol"] == "superadmin" or bool(user["es_superadmin"])
    ):
        session["rol"] = "superadmin"
        session.pop("agencia_id", None)
        return None
    if user is None or not user["agencia_id"] or user["estado"] != "activa":
        session.clear()
        return redirect(url_for("login", suspended="1"))
    session["agencia_id"] = int(user["agencia_id"])
    session["rol"] = user["rol"]
    return None


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


def _is_password_hash(value: str) -> bool:
    return bool(PASSWORD_HASH_RE.fullmatch(value))


def _migrate_password_hashes(connection: DatabaseConnection) -> None:
    users = connection.execute(
        "SELECT id, password, password_hash FROM usuarios"
    ).fetchall()
    for user in users:
        stored_password = user["password"] or ""
        stored_hash = user["password_hash"] or ""
        if _is_password_hash(stored_hash):
            password_hash = stored_hash
        elif _is_password_hash(stored_password):
            password_hash = stored_password
        elif stored_password:
            password_hash = generate_password_hash(stored_password)
        elif stored_hash:
            password_hash = generate_password_hash(stored_hash)
        else:
            password_hash = ""
        connection.execute(
            "UPDATE usuarios SET password = '', password_hash = ? WHERE id = ?",
            (password_hash, user["id"]),
        )


def _migrate_users_role_constraint(connection: DatabaseConnection) -> None:
    if connection.is_postgres:
        constraints = connection.execute(
            """
            SELECT c.conname AS name,
                   pg_get_constraintdef(c.oid) AS definition
            FROM pg_constraint AS c
            JOIN pg_class AS t ON t.oid = c.conrelid
            WHERE c.contype = 'c' AND t.relname = 'usuarios'
              AND pg_get_constraintdef(c.oid) ILIKE '%%rol%%'
            """
        ).fetchall()
        if not any(
            "superadmin" in str(constraint["definition"]).lower()
            for constraint in constraints
        ):
            for constraint in constraints:
                name = str(constraint["name"]).replace('"', '""')
                connection.execute(
                    f'ALTER TABLE usuarios DROP CONSTRAINT "{name}"'
                )
            connection.execute(
                "ALTER TABLE usuarios ADD CONSTRAINT usuarios_rol_check "
                "CHECK (rol IN ('admin', 'asesor', 'superadmin'))"
            )
        connection.execute(
            "UPDATE usuarios SET es_superadmin = TRUE "
            "WHERE LOWER(COALESCE(rol, '')) = 'superadmin'"
        )
        return

    table_sql = connection.execute(
        "SELECT sql FROM sqlite_master WHERE type = 'table' AND name = 'usuarios'"
    ).fetchone()["sql"]
    if "'superadmin'" in table_sql:
        connection.execute(
            "UPDATE usuarios SET es_superadmin = TRUE "
            "WHERE LOWER(COALESCE(rol, '')) = 'superadmin'"
        )
        return

    connection.execute(
        """
        CREATE TABLE usuarios_migrated (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            username TEXT NOT NULL UNIQUE,
            password TEXT NOT NULL DEFAULT '',
            rol TEXT NOT NULL DEFAULT 'asesor'
                CHECK (rol IN ('admin', 'asesor', 'superadmin')),
            nombre_completo TEXT NOT NULL DEFAULT '',
            email TEXT UNIQUE,
            password_hash TEXT,
            nombre TEXT,
            es_admin BOOLEAN DEFAULT FALSE,
            es_superadmin BOOLEAN NOT NULL DEFAULT FALSE,
            agencia_id INTEGER REFERENCES agencias(id),
            fecha_creacion TEXT DEFAULT CURRENT_TIMESTAMP
        )
        """
    )
    connection.execute(
        """
        INSERT INTO usuarios_migrated (
            id, username, password, rol, nombre_completo, email, password_hash,
            nombre, es_admin, es_superadmin, agencia_id, fecha_creacion
        )
        SELECT id, username, COALESCE(password, ''), rol,
               COALESCE(nombre_completo, ''), email, password_hash, nombre,
               es_admin, COALESCE(es_superadmin, FALSE), agencia_id, fecha_creacion
        FROM usuarios
        """
    )
    connection.execute("DROP TABLE usuarios")
    connection.execute("ALTER TABLE usuarios_migrated RENAME TO usuarios")


def _migrate_period_tenant_key(connection: DatabaseConnection) -> None:
    if connection.is_postgres:
        constraints = connection.execute(
            """
            SELECT c.conname AS name, pg_get_constraintdef(c.oid) AS definition
            FROM pg_constraint AS c
            JOIN pg_class AS t ON t.oid = c.conrelid
            WHERE t.relname = 'periodos_cierre' AND c.contype = 'u'
            """
        ).fetchall()
        has_tenant_key = False
        for constraint in constraints:
            definition = str(constraint["definition"])
            if "agencia_id" in definition and "nombre_periodo" in definition:
                has_tenant_key = True
            elif "nombre_periodo" in definition:
                name = str(constraint["name"]).replace('"', '""')
                connection.execute(
                    f'ALTER TABLE periodos_cierre DROP CONSTRAINT "{name}"'
                )
        if not has_tenant_key:
            connection.execute(
                "ALTER TABLE periodos_cierre ADD CONSTRAINT "
                "periodos_cierre_agencia_periodo_key "
                "UNIQUE (agencia_id, nombre_periodo)"
            )
        connection.execute(
            "ALTER TABLE periodos_cierre ALTER COLUMN agencia_id SET NOT NULL"
        )
        return

    table_sql = connection.execute(
        "SELECT sql FROM sqlite_master "
        "WHERE type = 'table' AND name = 'periodos_cierre'"
    ).fetchone()["sql"]
    if "UNIQUE (agencia_id, nombre_periodo)" in table_sql:
        return
    connection.execute(
        """
        CREATE TABLE periodos_cierre_migrated (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            nombre_periodo TEXT NOT NULL,
            agencia_id INTEGER NOT NULL REFERENCES agencias(id),
            fecha_cierre TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
            usuario_cierre_id INTEGER,
            estado TEXT NOT NULL DEFAULT 'activo'
                CHECK (estado IN ('activo', 'cerrado')),
            UNIQUE (agencia_id, nombre_periodo),
            FOREIGN KEY (usuario_cierre_id) REFERENCES usuarios(id)
        )
        """
    )
    connection.execute(
        """
        INSERT INTO periodos_cierre_migrated (
            id, nombre_periodo, agencia_id, fecha_cierre,
            usuario_cierre_id, estado
        )
        SELECT id, nombre_periodo, agencia_id, fecha_cierre,
               usuario_cierre_id, estado
        FROM periodos_cierre
        """
    )
    connection.execute("DROP TABLE periodos_cierre")
    connection.execute(
        "ALTER TABLE periodos_cierre_migrated RENAME TO periodos_cierre"
    )


def _migrate_closure_tenant_keys(
    connection: DatabaseConnection, default_agency_id: int
) -> None:
    _add_column(
        connection, "cierres_periodo", "agencia_id",
        "INTEGER REFERENCES agencias(id)",
    )
    _add_column(
        connection, "cierres_prepaga", "agencia_id",
        "INTEGER REFERENCES agencias(id)",
    )
    connection.execute(
        "UPDATE cierres_periodo SET agencia_id = ? WHERE agencia_id IS NULL",
        (default_agency_id,),
    )
    connection.execute(
        "UPDATE cierres_prepaga SET agencia_id = ? WHERE agencia_id IS NULL",
        (default_agency_id,),
    )
    if connection.is_postgres:
        for table, columns in (
            ("cierres_periodo", ("periodo",)),
            ("cierres_prepaga", ("periodo", "prepaga")),
        ):
            constraints = connection.execute(
                """
                SELECT conname AS name, pg_get_constraintdef(oid) AS definition
                FROM pg_constraint
                WHERE conrelid = ?::regclass AND contype = 'p'
                """,
                (table,),
            ).fetchall()
            key_columns = ", ".join(("agencia_id", *columns))
            expected_key = f"({key_columns})"
            if not any(
                expected_key in str(constraint["definition"]).replace('"', '')
                for constraint in constraints
            ):
                for constraint in constraints:
                    name = str(constraint["name"]).replace('"', '""')
                    connection.execute(
                        f'ALTER TABLE {table} DROP CONSTRAINT "{name}"'
                    )
                connection.execute(
                    f"ALTER TABLE {table} ADD PRIMARY KEY ({key_columns})"
                )
            connection.execute(
                f"ALTER TABLE {table} ALTER COLUMN agencia_id SET NOT NULL"
            )
        return

    for table, columns in (
        ("cierres_periodo", ("periodo",)),
        ("cierres_prepaga", ("periodo", "prepaga")),
    ):
        table_sql = connection.execute(
            "SELECT sql FROM sqlite_master WHERE type = 'table' AND name = ?",
            (table,),
        ).fetchone()["sql"]
        tenant_key = f"PRIMARY KEY (agencia_id, {', '.join(columns)})"
        if tenant_key in table_sql:
            continue
        replacement = f"{table}_migrated"
        selected_columns = ", ".join(("periodo", *columns[1:], "agencia_id",
                                      "fecha_cierre", "cerrado_por"))
        key_columns = ", ".join(("agencia_id", *columns))
        create_columns = (
            "periodo TEXT NOT NULL, agencia_id INTEGER NOT NULL "
            "REFERENCES agencias(id), "
        )
        if table == "cierres_prepaga":
            create_columns += "prepaga TEXT NOT NULL, "
        create_columns += (
            "fecha_cierre TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP, "
            "cerrado_por INTEGER, "
            f"PRIMARY KEY ({key_columns}), "
            "FOREIGN KEY (cerrado_por) REFERENCES usuarios(id)"
        )
        connection.execute(
            f"CREATE TABLE {replacement} ({create_columns})"
        )
        connection.execute(
            f"INSERT INTO {replacement} ({selected_columns}) "
            f"SELECT {selected_columns} FROM {table}"
        )
        connection.execute(f"DROP TABLE {table}")
        connection.execute(f"ALTER TABLE {replacement} RENAME TO {table}")


def init_db() -> None:
    """Crea las tablas nuevas y migra de forma aditiva las instalaciones previas."""
    with db_connection() as connection:
        if not connection.is_postgres:
            connection.execute("PRAGMA foreign_keys = OFF")
        user_id_type = "SERIAL PRIMARY KEY" if connection.is_postgres else (
            "INTEGER PRIMARY KEY AUTOINCREMENT"
        )
        ficha_id_type = user_id_type
        connection.execute(
            f"""
            CREATE TABLE IF NOT EXISTS agencias (
                id {user_id_type},
                nombre_agencia TEXT NOT NULL,
                dominio TEXT NOT NULL UNIQUE,
                estado TEXT NOT NULL DEFAULT 'activa'
                    CHECK (estado IN ('activa', 'suspendida')),
                fecha_alta TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
                proximo_vencimiento TEXT
            )
            """
        )
        default_agency_date = date.today().isoformat()
        connection.execute(
            """
            INSERT INTO agencias (
                nombre_agencia, dominio, estado, fecha_alta, proximo_vencimiento
            ) VALUES (?, 'broker.local', 'activa', ?, ?)
            ON CONFLICT (dominio) DO NOTHING
            """,
            (os.environ.get("DEFAULT_AGENCY_NAME", "Agencia Principal"),
             default_agency_date, default_agency_date),
        )
        default_agency = connection.execute(
            "SELECT id FROM agencias WHERE dominio = 'broker.local'"
        ).fetchone()
        if default_agency is None:
            raise RuntimeError("No se pudo inicializar la agencia predeterminada.")
        default_agency_id = int(default_agency["id"])
        connection.execute(
            f"""
            CREATE TABLE IF NOT EXISTS usuarios (
                id {user_id_type},
                username TEXT NOT NULL UNIQUE,
                password TEXT NOT NULL DEFAULT '',
                rol TEXT NOT NULL DEFAULT 'asesor'
                    CHECK (rol IN ('admin', 'asesor', 'superadmin')),
                nombre_completo TEXT NOT NULL DEFAULT '',
                email TEXT UNIQUE,
                password_hash TEXT,
                nombre TEXT,
                es_admin BOOLEAN DEFAULT FALSE,
                es_superadmin BOOLEAN NOT NULL DEFAULT FALSE,
                agencia_id INTEGER REFERENCES agencias(id),
                fecha_creacion TEXT DEFAULT CURRENT_TIMESTAMP
            )
            """
        )
        connection.execute(
            f"""
            CREATE TABLE IF NOT EXISTS periodos_cierre (
                id {user_id_type},
                nombre_periodo TEXT NOT NULL,
                agencia_id INTEGER NOT NULL REFERENCES agencias(id),
                fecha_cierre TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
                usuario_cierre_id INTEGER,
                estado TEXT NOT NULL DEFAULT 'activo'
                    CHECK (estado IN ('activo', 'cerrado')),
                UNIQUE (agencia_id, nombre_periodo),
                FOREIGN KEY (usuario_cierre_id) REFERENCES usuarios(id)
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
                empresa TEXT,
                clave_fiscal TEXT,
                telefono TEXT,
                grupo_familiar TEXT NOT NULL DEFAULT 'Sin especificar',
                sueldo_bruto REAL DEFAULT 0,
                aporte REAL DEFAULT 0,
                porcentaje_comision REAL DEFAULT 1,
                periodo_cierre_id INTEGER,
                porcentaje_comision_cierre REAL,
                importe_comision_cierre REAL,
                comision_liquidada_cierre REAL,
                motivo_rechazo TEXT,
                agencia_id INTEGER REFERENCES agencias(id),
                fecha_creacion TEXT DEFAULT CURRENT_TIMESTAMP,
                FOREIGN KEY (asesor_id) REFERENCES usuarios(id),
                FOREIGN KEY (periodo_cierre_id) REFERENCES periodos_cierre(id)
            )
            """
        )
        connection.execute(
            f"""
            CREATE TABLE IF NOT EXISTS prepagas_config (
                id {user_id_type},
                usuario_id INTEGER NOT NULL,
                prepaga TEXT NOT NULL,
                porcentaje_comision INTEGER NOT NULL DEFAULT 0
                    CHECK (porcentaje_comision >= 0),
                activa BOOLEAN NOT NULL DEFAULT TRUE,
                agencia_id INTEGER REFERENCES agencias(id),
                UNIQUE (usuario_id, prepaga),
                FOREIGN KEY (usuario_id) REFERENCES usuarios(id) ON DELETE CASCADE
            )
            """
        )
        _migrate_prepaga_percentage(connection)

        for name, declaration in (
            ("username", "TEXT"),
            ("password", "TEXT"),
            ("rol", "TEXT NOT NULL DEFAULT 'asesor'"),
            ("nombre_completo", "TEXT"),
            ("email", "TEXT"),
            ("password_hash", "TEXT"),
            ("nombre", "TEXT"),
            ("es_admin", "BOOLEAN DEFAULT FALSE"),
            ("es_superadmin", "BOOLEAN NOT NULL DEFAULT FALSE"),
            ("agencia_id", "INTEGER REFERENCES agencias(id)"),
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
            ("empresa", "TEXT"),
            ("clave_fiscal", "TEXT"),
            ("telefono", "TEXT"),
            ("grupo_familiar", "TEXT NOT NULL DEFAULT 'Sin especificar'"),
            ("sueldo_bruto", "REAL DEFAULT 0"),
            ("aporte", "REAL DEFAULT 0"),
            ("porcentaje_comision", "REAL DEFAULT 1"),
            ("periodo_cierre_id", "INTEGER REFERENCES periodos_cierre(id)"),
            ("porcentaje_comision_cierre", "REAL"),
            ("importe_comision_cierre", "REAL"),
            ("comision_liquidada_cierre", "REAL"),
            ("motivo_rechazo", "TEXT"),
            ("agencia_id", "INTEGER REFERENCES agencias(id)"),
            ("fecha_creacion", "TEXT"),
        )
        for name, declaration in ficha_columns:
            _add_column(connection, "fichas", name, declaration)

        _add_column(
            connection, "periodos_cierre", "agencia_id",
            "INTEGER REFERENCES agencias(id)",
        )
        _add_column(
            connection, "prepagas_config", "agencia_id",
            "INTEGER REFERENCES agencias(id)",
        )
        connection.execute(
            "UPDATE usuarios SET agencia_id = ? "
            "WHERE agencia_id IS NULL AND COALESCE(es_superadmin, FALSE) = FALSE",
            (default_agency_id,),
        )
        connection.execute(
            """
            UPDATE fichas
            SET agencia_id = COALESCE(
                (SELECT agencia_id FROM usuarios WHERE usuarios.id = fichas.asesor_id),
                ?
            )
            WHERE agencia_id IS NULL
            """,
            (default_agency_id,),
        )
        connection.execute(
            """
            UPDATE prepagas_config
            SET agencia_id = COALESCE(
                (SELECT agencia_id FROM usuarios
                 WHERE usuarios.id = prepagas_config.usuario_id),
                ?
            )
            WHERE agencia_id IS NULL
            """,
            (default_agency_id,),
        )
        connection.execute(
            "UPDATE periodos_cierre SET agencia_id = ? WHERE agencia_id IS NULL",
            (default_agency_id,),
        )
        if connection.is_postgres:
            connection.execute(
                "ALTER TABLE fichas ALTER COLUMN agencia_id SET NOT NULL"
            )
            connection.execute(
                "ALTER TABLE prepagas_config ALTER COLUMN agencia_id SET NOT NULL"
            )
        _migrate_users_role_constraint(connection)
        _migrate_period_tenant_key(connection)

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
                    WHEN es_superadmin IS TRUE THEN 'superadmin'
                    WHEN LOWER(COALESCE(rol, '')) = 'admin'
                         OR es_admin IS TRUE THEN 'admin'
                    ELSE 'asesor'
                END
            """
        )
        _migrate_password_hashes(connection)
        connection.execute(
            "UPDATE fichas SET clave_fiscal = NULL WHERE clave_fiscal IS NOT NULL"
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
            "CREATE INDEX IF NOT EXISTS idx_fichas_periodo_cierre "
            "ON fichas(periodo_cierre_id, asesor_id)"
        )
        connection.execute(
            "CREATE INDEX IF NOT EXISTS idx_fichas_estado_prepaga "
            "ON fichas(estado, prepaga)"
        )
        connection.execute(
            "CREATE INDEX IF NOT EXISTS idx_fichas_agencia_periodo_asesor "
            "ON fichas(agencia_id, periodo, asesor_id)"
        )
        connection.execute(
            "CREATE INDEX IF NOT EXISTS idx_usuarios_agencia_rol "
            "ON usuarios(agencia_id, rol)"
        )
        connection.execute(
            "CREATE INDEX IF NOT EXISTS idx_prepagas_agencia_usuario "
            "ON prepagas_config(agencia_id, usuario_id, prepaga)"
        )
        connection.execute(
            """
            CREATE TABLE IF NOT EXISTS cierres_periodo (
                periodo TEXT NOT NULL,
                agencia_id INTEGER NOT NULL REFERENCES agencias(id),
                fecha_cierre TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
                cerrado_por INTEGER,
                PRIMARY KEY (agencia_id, periodo),
                FOREIGN KEY (cerrado_por) REFERENCES usuarios(id)
            )
            """
        )
        connection.execute(
            """
            CREATE TABLE IF NOT EXISTS cierres_prepaga (
                periodo TEXT NOT NULL,
                agencia_id INTEGER NOT NULL REFERENCES agencias(id),
                prepaga TEXT NOT NULL,
                fecha_cierre TEXT NOT NULL DEFAULT CURRENT_TIMESTAMP,
                cerrado_por INTEGER,
                PRIMARY KEY (agencia_id, periodo, prepaga),
                FOREIGN KEY (cerrado_por) REFERENCES usuarios(id)
            )
            """
        )
        _migrate_closure_tenant_keys(connection, default_agency_id)
        legacy_closures = connection.execute(
            """
            SELECT periodo, fecha_cierre, cerrado_por, 1 AS cierre_global
            FROM cierres_periodo
            UNION ALL
            SELECT periodo, fecha_cierre, cerrado_por, 0 AS cierre_global
            FROM cierres_prepaga
            """
        ).fetchall()
        period_closures: dict[str, dict[str, Any]] = {}
        for closure in legacy_closures:
            name = closure["periodo"]
            if not name:
                continue
            data = period_closures.setdefault(
                name,
                {
                    "global": False,
                    "fecha_cierre": closure["fecha_cierre"],
                    "usuario_cierre_id": closure["cerrado_por"],
                },
            )
            if closure["cierre_global"]:
                data["global"] = True
                data["fecha_cierre"] = closure["fecha_cierre"]
                data["usuario_cierre_id"] = closure["cerrado_por"]
        for name, data in period_closures.items():
            status = "cerrado" if data["global"] else "activo"
            connection.execute(
                """
                INSERT INTO periodos_cierre (
                    nombre_periodo, agencia_id, fecha_cierre,
                    usuario_cierre_id, estado
                ) VALUES (?, ?, ?, ?, ?)
                ON CONFLICT (agencia_id, nombre_periodo) DO NOTHING
                """,
                (
                    name,
                    default_agency_id,
                    data["fecha_cierre"],
                    data["usuario_cierre_id"],
                    status,
                ),
            )
            if data["global"]:
                connection.execute(
                    """
                    UPDATE periodos_cierre SET estado = 'cerrado'
                    WHERE nombre_periodo = ? AND agencia_id = ?
                    """,
                    (name, default_agency_id),
                )
        connection.execute(
            """
            UPDATE fichas
            SET periodo_cierre_id = (
                    SELECT id FROM periodos_cierre
                    WHERE nombre_periodo = fichas.periodo
                      AND agencia_id = fichas.agencia_id
                ),
                porcentaje_comision_cierre = COALESCE(
                    porcentaje_comision_cierre, porcentaje_comision
                ),
                importe_comision_cierre = COALESCE(
                    importe_comision_cierre, importe_comision
                ),
                comision_liquidada_cierre = COALESCE(
                    comision_liquidada_cierre,
                    CASE WHEN estado = 'APROBADA'
                         THEN importe_comision ELSE 0 END
                )
            WHERE EXISTS (
                    SELECT 1 FROM cierres_periodo
                    WHERE cierres_periodo.periodo = fichas.periodo
                      AND cierres_periodo.agencia_id = fichas.agencia_id
                )
               OR EXISTS (
                    SELECT 1 FROM cierres_prepaga
                    WHERE cierres_prepaga.periodo = fichas.periodo
                      AND cierres_prepaga.prepaga = fichas.prepaga
                      AND cierres_prepaga.agencia_id = fichas.agencia_id
                )
            """
        )
        active_period = _active_period(connection, agency_id=default_agency_id)
        connection.execute(
            """
            INSERT INTO periodos_cierre (nombre_periodo, agencia_id, estado)
            VALUES (?, ?, 'activo')
            ON CONFLICT (agencia_id, nombre_periodo) DO NOTHING
            """,
            (active_period, default_agency_id),
        )
        users = connection.execute(
            "SELECT id, agencia_id FROM usuarios WHERE agencia_id IS NOT NULL"
        ).fetchall()
        for user in users:
            _ensure_default_prepagas(
                connection, int(user["id"]), int(user["agencia_id"])
            )
        if not connection.is_postgres:
            connection.execute("PRAGMA foreign_keys = ON")


def _ensure_default_prepagas(
    connection: DatabaseConnection, user_id: int, agency_id: int | None = None
) -> None:
    user = connection.execute(
        "SELECT agencia_id FROM usuarios WHERE id = ?", (user_id,)
    ).fetchone()
    if agency_id is None:
        agency_id = int(user["agencia_id"]) if user and user["agencia_id"] else None
    for prepaga in DEFAULT_PREPAGAS:
        connection.execute(
            """
            INSERT INTO prepagas_config (
                usuario_id, prepaga, porcentaje_comision, activa, agencia_id
            ) VALUES (?, ?, 0, TRUE, ?)
            ON CONFLICT (usuario_id, prepaga) DO NOTHING
            """,
            (user_id, prepaga, agency_id),
        )


def _migrate_prepaga_percentage(connection: DatabaseConnection) -> None:
    if connection.is_postgres:
        constraints = connection.execute(
            """
            SELECT c.conname AS constraint_name,
                   pg_get_constraintdef(c.oid) AS check_clause
            FROM pg_constraint AS c
            JOIN pg_class AS t ON t.oid = c.conrelid
            JOIN pg_namespace AS n ON n.oid = t.relnamespace
            WHERE c.contype = 'c'
              AND t.relname = 'prepagas_config'
              AND n.nspname = current_schema()
            """
        ).fetchall()
        for constraint in constraints:
            check_clause = str(constraint["check_clause"])
            if re.search(
                r"porcentaje_comision\s*<=\s*\(?100\b",
                check_clause,
                flags=re.IGNORECASE,
            ):
                constraint_name = str(constraint["constraint_name"]).replace(
                    '"', '""'
                )
                connection.execute(
                    "ALTER TABLE prepagas_config DROP CONSTRAINT "
                    f'"{constraint_name}"'
                )
        percentage_column = connection.execute(
            """
            SELECT data_type FROM information_schema.columns
            WHERE table_schema = current_schema()
              AND table_name = 'prepagas_config'
              AND column_name = 'porcentaje_comision'
            """
        ).fetchone()
        if percentage_column["data_type"] != "integer":
            connection.execute(
                "ALTER TABLE prepagas_config ALTER COLUMN porcentaje_comision "
                "TYPE INTEGER USING TRUNC(porcentaje_comision)::INTEGER"
            )
        return

    table_sql = connection.execute(
        "SELECT sql FROM sqlite_master "
        "WHERE type = 'table' AND name = 'prepagas_config'"
    ).fetchone()["sql"]
    if "porcentaje_comision REAL" not in table_sql and "<= 100" not in table_sql:
        return

    connection.execute(
        """
        CREATE TABLE prepagas_config_migrated (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            usuario_id INTEGER NOT NULL,
            prepaga TEXT NOT NULL,
            porcentaje_comision INTEGER NOT NULL DEFAULT 0
                CHECK (porcentaje_comision >= 0),
            activa BOOLEAN NOT NULL DEFAULT TRUE,
            UNIQUE (usuario_id, prepaga),
            FOREIGN KEY (usuario_id) REFERENCES usuarios(id) ON DELETE CASCADE
        )
        """
    )
    connection.execute(
        """
        INSERT INTO prepagas_config_migrated (
            id, usuario_id, prepaga, porcentaje_comision, activa
        )
        SELECT id, usuario_id, prepaga, CAST(porcentaje_comision AS INTEGER), activa
        FROM prepagas_config
        """
    )
    connection.execute("DROP TABLE prepagas_config")
    connection.execute(
        "ALTER TABLE prepagas_config_migrated RENAME TO prepagas_config"
    )


def _month_after(period: str) -> str:
    year, month = map(int, period.split("-"))
    return f"{year + (month == 12):04d}-{1 if month == 12 else month + 1:02d}"


def _active_period(
    connection: DatabaseConnection,
    prepaga: str | None = None,
    agency_id: int | None = None,
) -> str:
    current_period = date.today().strftime("%Y-%m")
    if agency_id is None:
        agency_id = _session_agency_id()
    if agency_id is None:
        default_agency = connection.execute(
            "SELECT id FROM agencias WHERE dominio = 'broker.local'"
        ).fetchone()
        agency_id = int(default_agency["id"]) if default_agency else None
    agency_clause = " AND agencia_id = ?" if agency_id is not None else ""
    agency_values: tuple[Any, ...] = (agency_id,) if agency_id is not None else ()
    if prepaga is None:
        last_closed = connection.execute(
            "SELECT MAX(periodo) AS periodo FROM cierres_periodo "
            f"WHERE 1 = 1{agency_clause}",
            agency_values,
        ).fetchone()["periodo"]
    else:
        last_closed = connection.execute(
            """
            SELECT MAX(periodo) AS periodo FROM (
                SELECT periodo FROM cierres_periodo
                WHERE 1 = 1
                  AND (? IS NULL OR agencia_id = ?)
                UNION ALL
                SELECT periodo FROM cierres_prepaga
                WHERE prepaga = ? AND (? IS NULL OR agencia_id = ?)
            )
            """,
            (
                agency_id, agency_id, prepaga, agency_id, agency_id,
            ),
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
    agency_id = _session_agency_id()
    agency_clause = " AND agencia_id = ?" if agency_id is not None else ""
    agency_values: tuple[Any, ...] = (agency_id,) if agency_id is not None else ()
    prepagas = (
        [prepaga_filter]
        if prepaga_filter
        else [
            row["prepaga"]
            for row in connection.execute(
                "SELECT DISTINCT prepaga, LOWER(prepaga) AS prepaga_sort FROM fichas "
                "WHERE prepaga IS NOT NULL AND prepaga != ''"
                f"{agency_clause} "
                "ORDER BY prepaga_sort",
                agency_values,
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
        active_values.extend((prepaga, _active_period(
            connection, prepaga, agency_id
        )))
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


def format_date(value: Any) -> str:
    if not value:
        return "-"
    try:
        parsed = datetime.fromisoformat(str(value).replace("Z", "+00:00"))
    except ValueError:
        try:
            parsed = datetime.strptime(str(value), "%Y-%m-%d")
        except ValueError:
            return str(value)
    return parsed.strftime("%d/%m/%Y")


def _ensure_period_record(
    connection: DatabaseConnection,
    period: str,
    status: str = "activo",
    user_id: int | None = None,
    agency_id: int | None = None,
) -> int:
    if agency_id is None:
        agency_id = _session_agency_id()
    if agency_id is None:
        agency = connection.execute(
            "SELECT id FROM agencias WHERE dominio = 'broker.local'"
        ).fetchone()
        if agency is None:
            raise RuntimeError("No se encontró una agencia para el período.")
        agency_id = int(agency["id"])
    connection.execute(
        """
        INSERT INTO periodos_cierre (
            nombre_periodo, agencia_id, usuario_cierre_id, estado
        ) VALUES (?, ?, ?, ?)
        ON CONFLICT (agencia_id, nombre_periodo) DO NOTHING
        """,
        (period, agency_id, user_id, status),
    )
    row = connection.execute(
        "SELECT id FROM periodos_cierre "
        "WHERE nombre_periodo = ? AND agencia_id = ?",
        (period, agency_id),
    ).fetchone()
    if row is None:
        raise RuntimeError(f"No se pudo obtener el registro del período {period}.")
    return int(row["id"])


def _snapshot_closed_fichas(
    connection: DatabaseConnection,
    period_id: int,
    where_clause: str,
    values: tuple[Any, ...],
) -> int:
    result = connection.execute(
        f"""
        UPDATE fichas
        SET periodo_cierre_id = ?,
            porcentaje_comision_cierre = porcentaje_comision,
            importe_comision_cierre = importe_comision,
            comision_liquidada_cierre = CASE
                WHEN estado = 'APROBADA' THEN COALESCE(importe_comision, 0)
                ELSE 0
            END
        WHERE {where_clause} AND periodo_cierre_id IS NULL
        """,
        (period_id, *values),
    )
    return max(result.rowcount, 0)


app.jinja_env.filters["ars"] = format_ars
app.jinja_env.filters["fecha"] = format_date


def _dict_ficha(row: Any) -> dict[str, Any]:
    ficha = dict(row)
    ficha["estado"] = str(ficha.get("estado") or "PENDIENTE").upper()
    ficha["nombre_afiliado"] = ficha.get("cliente_nombre") or ""
    ficha["cuil_afiliado"] = ficha.get("cuil") or ""
    if ficha.get("importe_comision_cierre") is not None:
        ficha["importe_comision"] = ficha["importe_comision_cierre"]
    if ficha.get("porcentaje_comision_cierre") is not None:
        ficha["porcentaje_comision"] = ficha["porcentaje_comision_cierre"]
    ficha["monto_comision"] = ficha.get("importe_comision") or 0
    if ficha.get("comision_liquidada_cierre") is not None:
        ficha["comision_a_liquidar"] = ficha["comision_liquidada_cierre"]
    else:
        ficha["comision_a_liquidar"] = (
            ficha["monto_comision"] if ficha["estado"] == "APROBADA" else 0
        )
    ficha["aporte"] = ficha.get("aporte") or 0
    ficha["porcentaje_comision"] = ficha.get("porcentaje_comision") or 0
    ficha["fecha_creacion"] = ficha.get("fecha_carga") or ""
    ficha["asesor_nombre"] = ficha.get("nombre_completo") or "Asesor"
    return ficha


def _dashboard_filters() -> tuple[list[str], list[Any], str, str, str, str | None]:
    agency_id = _session_agency_id()
    clauses: list[str] = ["f.agencia_id = ?"]
    values: list[Any] = [agency_id]

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


def superadmin_required(view: Any) -> Any:
    @wraps(view)
    def wrapped(*args: Any, **kwargs: Any) -> Any:
        if "user_id" not in session:
            return redirect(url_for("login", next=request.full_path.rstrip("?")))
        if session.get("rol") != "superadmin":
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


def _session_user_is_admin() -> bool:
    with db_connection() as connection:
        user = connection.execute(
            """
            SELECT rol, es_admin FROM usuarios
            WHERE id = ? AND agencia_id = ?
            """,
            (session["user_id"], _session_agency_id()),
        ).fetchone()
    return user is not None and (
        user["rol"] == "admin" or bool(user["es_admin"])
    )


def _session_agency_id() -> int | None:
    if not has_request_context():
        return None
    agency_id = session.get("agencia_id")
    return int(agency_id) if str(agency_id or "").isdecimal() else None


def _require_prepaga_config_admin() -> Any | None:
    if _session_user_is_admin():
        return None
    flash("No tienes permisos para acceder a esta sección", "warning")
    return redirect(url_for("mis_fichas"))


def _password_matches(stored_password: str, supplied_password: str) -> bool:
    if not stored_password:
        return False
    try:
        return check_password_hash(stored_password, supplied_password)
    except (ValueError, TypeError):
        return False


def _email_matches_domain(email: str, domain: str) -> bool:
    return bool(
        re.fullmatch(
            r"[A-Z0-9._%+-]+@" + re.escape(domain),
            email,
            flags=re.IGNORECASE,
        )
    )


@app.get("/")
def index() -> Any:
    if session.get("rol") == "superadmin":
        return redirect(url_for("superadmin"))
    if session.get("rol") == "admin":
        return redirect(url_for("admin_dashboard"))
    if session.get("rol") == "asesor":
        return redirect(url_for("mis_fichas"))
    return redirect(url_for("login"))


@app.route("/login", methods=["GET", "POST"])
def login() -> Any:
    if request.method == "GET":
        if request.args.get("suspended") == "1":
            return render_template(
                "login.html",
                error=(
                    "Tu suscripción se encuentra suspendida. Ponte en contacto "
                    "con soporte para regularizar tu cuota."
                ),
            )
        if session.get("rol") == "superadmin":
            return redirect(url_for("superadmin"))
        if session.get("rol") == "admin":
            return redirect(url_for("admin_dashboard"))
        return render_template("login.html", error=None)

    identity = (request.form.get("email") or request.form.get("username") or "").strip()
    password = request.form.get("password", "")
    with db_connection() as connection:
        user = connection.execute(
            """
            SELECT u.id, u.username, u.password_hash, u.rol, u.nombre_completo,
                   u.agencia_id, u.es_superadmin, a.estado AS agencia_estado
            FROM usuarios AS u
            LEFT JOIN agencias AS a ON a.id = u.agencia_id
            WHERE LOWER(username) = LOWER(?) OR LOWER(COALESCE(email, '')) = LOWER(?)
            LIMIT 1
            """,
            (identity, identity),
        ).fetchone()
    if user is None or not _password_matches(user["password_hash"] or "", password):
        return render_template("login.html", error="Usuario o contraseña incorrectos."), 401

    if user["rol"] != "superadmin" and not bool(user["es_superadmin"]):
        if user["agencia_estado"] != "activa":
            return render_template(
                "login.html",
                error=(
                    "Tu suscripción se encuentra suspendida. Ponte en contacto "
                    "con soporte para regularizar tu cuota."
                ),
            ), 403
    if user["rol"] == "asesor":
        with db_connection() as connection:
            _ensure_default_prepagas(
                connection, int(user["id"]), int(user["agencia_id"])
            )

    session.clear()
    session["user_id"] = user["id"]
    session["username"] = user["username"]
    session["nombre"] = user["nombre_completo"] or user["username"]
    effective_role = (
        "superadmin"
        if user["rol"] == "superadmin" or bool(user["es_superadmin"])
        else user["rol"]
    )
    session["rol"] = effective_role
    if user["agencia_id"] is not None:
        session["agencia_id"] = int(user["agencia_id"])
    if effective_role == "superadmin":
        return redirect(url_for("superadmin"))
    if user["rol"] == "admin":
        return redirect(url_for("admin_dashboard"))
    return redirect(url_for("mis_fichas"))


@app.cli.command("crear-superadmin")
def crear_superadmin() -> None:
    """Crea o actualiza el SuperAdmin usando credenciales entregadas por entorno."""
    username = os.environ.get("SUPERADMIN_USERNAME", "").strip()
    password = os.environ.get("SUPERADMIN_PASSWORD", "")
    if not username or len(password) < 12:
        raise click.ClickException(
            "Define SUPERADMIN_USERNAME y SUPERADMIN_PASSWORD (mínimo 12 "
            "caracteres) en el entorno antes de crear el SuperAdmin."
        )
    with db_connection() as connection:
        existing = connection.execute(
            """
            SELECT id FROM usuarios
            WHERE LOWER(username) = LOWER(?) OR LOWER(COALESCE(email, '')) = LOWER(?)
            LIMIT 1
            """,
            (username, username),
        ).fetchone()
        password_hash = generate_password_hash(password)
        if existing:
            connection.execute(
                """
                UPDATE usuarios
                SET username = ?, password = '', password_hash = ?,
                    rol = 'superadmin', es_superadmin = TRUE, agencia_id = NULL
                WHERE id = ?
                """,
                (username, password_hash, existing["id"]),
            )
        else:
            connection.execute(
                """
                INSERT INTO usuarios (
                    username, email, password, password_hash, rol,
                    nombre_completo, es_superadmin, agencia_id
                ) VALUES (?, ?, '', ?, 'superadmin', ?, TRUE, NULL)
                """,
                (username, username if "@" in username else None,
                 password_hash, username),
            )
    click.echo("Cuenta SuperAdmin creada o actualizada correctamente.")


@app.route("/superadmin", methods=["GET", "POST"])
@superadmin_required
def superadmin() -> Any:
    error = None
    if request.method == "POST":
        action = request.form.get("action", "")
        with db_connection() as connection:
            if action == "crear_agencia":
                agency_name = request.form.get("nombre_agencia", "").strip()
                domain = request.form.get("dominio", "").strip().lower().rstrip(".")
                admin_email = request.form.get("admin_email", "").strip().lower()
                admin_name = request.form.get("admin_nombre", "").strip()
                password = request.form.get("admin_password", "")
                if (
                    not agency_name
                    or not re.fullmatch(
                        r"(?=.{1,253}$)(?:[a-z0-9](?:[a-z0-9-]{0,61}[a-z0-9])?\.)+"
                        r"[a-z]{2,63}",
                        domain,
                    )
                ):
                    error = "El nombre o dominio de la agencia no es válido."
                elif not _email_matches_domain(admin_email, domain):
                    error = f"El email del admin debe terminar en @{domain}."
                elif len(password) < 12:
                    error = "La contraseña inicial debe tener al menos 12 caracteres."
                elif connection.execute(
                    "SELECT 1 FROM agencias WHERE dominio = ?", (domain,)
                ).fetchone():
                    error = "Ya existe una agencia con ese dominio."
                elif connection.execute(
                    "SELECT 1 FROM usuarios WHERE LOWER(username) = LOWER(?) "
                    "OR LOWER(COALESCE(email, '')) = LOWER(?)",
                    (admin_email, admin_email),
                ).fetchone():
                    error = "Ya existe una cuenta con ese email."
                else:
                    today = date.today()
                    due_date = today + timedelta(days=30)
                    connection.execute(
                        """
                        INSERT INTO agencias (
                            nombre_agencia, dominio, estado, fecha_alta,
                            proximo_vencimiento
                        ) VALUES (?, ?, 'activa', ?, ?)
                        """,
                        (agency_name, domain, today.isoformat(), due_date.isoformat()),
                    )
                    agency = connection.execute(
                        "SELECT id FROM agencias WHERE dominio = ?", (domain,)
                    ).fetchone()
                    if agency is None:
                        raise RuntimeError("No se pudo crear la agencia.")
                    connection.execute(
                        """
                        INSERT INTO usuarios (
                            username, email, password, password_hash, rol,
                            nombre_completo, agencia_id
                        ) VALUES (?, ?, '', ?, 'admin', ?, ?)
                        """,
                        (
                            admin_email, admin_email,
                            generate_password_hash(password),
                            admin_name or agency_name, agency["id"],
                        ),
                    )
                    admin = connection.execute(
                        "SELECT id FROM usuarios WHERE username = ?",
                        (admin_email,),
                    ).fetchone()
                    _ensure_default_prepagas(
                        connection, int(admin["id"]), int(agency["id"])
                    )
                    flash("Agencia creada y usuario administrador aprovisionado.", "success")
                    return redirect(url_for("superadmin"))
            elif action in {"suspender", "activar"}:
                agency_id = request.form.get("agencia_id", "")
                if not agency_id.isdecimal() or int(agency_id) < 1:
                    abort(400, description="La agencia seleccionada no es válida.")
                status = "suspendida" if action == "suspender" else "activa"
                result = connection.execute(
                    "UPDATE agencias SET estado = ? WHERE id = ?",
                    (status, int(agency_id)),
                )
                if result.rowcount == 0:
                    abort(404)
                flash(f"Agencia {status} correctamente.", "success")
                return redirect(url_for("superadmin"))
            elif action == "extender":
                agency_id = request.form.get("agencia_id", "")
                days_raw = request.form.get("dias", "")
                if (
                    not agency_id.isdecimal()
                    or not days_raw.isdecimal()
                    or not 1 <= int(days_raw) <= 3650
                ):
                    abort(400, description="Indica una agencia y cantidad de días válida.")
                agency = connection.execute(
                    "SELECT proximo_vencimiento FROM agencias WHERE id = ?",
                    (int(agency_id),),
                ).fetchone()
                if agency is None:
                    abort(404)
                try:
                    current_due = date.fromisoformat(
                        agency["proximo_vencimiento"] or date.today().isoformat()
                    )
                except ValueError:
                    current_due = date.today()
                start_date = max(current_due, date.today())
                new_due = date.fromordinal(
                    start_date.toordinal() + int(days_raw)
                )
                connection.execute(
                    "UPDATE agencias SET proximo_vencimiento = ? WHERE id = ?",
                    (new_due.isoformat(), int(agency_id)),
                )
                flash("Vencimiento extendido correctamente.", "success")
                return redirect(url_for("superadmin"))
            else:
                abort(400, description="La acción seleccionada no es válida.")
        if error:
            flash(error, "error")
    with db_connection() as connection:
        agencies = [
            dict(row)
            for row in connection.execute(
                """
                SELECT a.*, COUNT(u.id) AS usuarios_total
                FROM agencias AS a
                LEFT JOIN usuarios AS u ON u.agencia_id = a.id
                GROUP BY a.id
                ORDER BY a.nombre_agencia
                """
            )
        ]
    return render_template(
        "superadmin.html", agencias=agencies, nombre=session.get("nombre", ""),
        es_admin=False, route="superadmin",
    )


@app.post("/logout")
def logout() -> Any:
    session.clear()
    return redirect(url_for("login"))


@app.route("/gestion-asesores", methods=["GET", "POST"])
@admin_required
def gestion_asesores() -> Any:
    agency_id = _session_agency_id()
    if request.method == "POST":
        email = request.form.get("email", "").strip().lower()
        full_name = request.form.get("nombre_completo", "").strip()
        password = request.form.get("password", "")
        if len(password) < 12:
            flash("La contraseña debe tener al menos 12 caracteres.", "error")
        else:
            with db_connection() as connection:
                agency = connection.execute(
                    "SELECT dominio FROM agencias WHERE id = ?", (agency_id,)
                ).fetchone()
                if agency is None:
                    abort(403)
                domain = str(agency["dominio"]).lower()
                if email and "@" not in email:
                    email = f"{email}@{domain}"
                if not _email_matches_domain(email, domain):
                    flash(
                        f"El email del asesor debe tener el formato usuario@{domain}.",
                        "error",
                    )
                elif connection.execute(
                    "SELECT 1 FROM usuarios WHERE LOWER(username) = LOWER(?) "
                    "OR LOWER(COALESCE(email, '')) = LOWER(?)",
                    (email, email),
                ).fetchone():
                    flash("Ya existe una cuenta con ese email.", "error")
                else:
                    connection.execute(
                        """
                        INSERT INTO usuarios (
                            username, email, password, password_hash, rol,
                            nombre_completo, agencia_id
                        ) VALUES (?, ?, '', ?, 'asesor', ?, ?)
                        """,
                        (
                            email, email, generate_password_hash(password),
                            full_name or email, agency_id,
                        ),
                    )
                    advisor = connection.execute(
                        "SELECT id FROM usuarios WHERE username = ? AND agencia_id = ?",
                        (email, agency_id),
                    ).fetchone()
                    _ensure_default_prepagas(
                        connection, int(advisor["id"]), agency_id
                    )
                    flash("Asesor creado correctamente.", "success")
                    return redirect(url_for("gestion_asesores"))
        return redirect(url_for("gestion_asesores"))

    with db_connection() as connection:
        agency = connection.execute(
            "SELECT nombre_agencia, dominio FROM agencias WHERE id = ?",
            (agency_id,),
        ).fetchone()
        advisors = [
            dict(row)
            for row in connection.execute(
                """
                SELECT id, username, nombre_completo, fecha_creacion
                FROM usuarios
                WHERE agencia_id = ? AND rol = 'asesor'
                ORDER BY LOWER(nombre_completo), id
                """,
                (agency_id,),
            )
        ]
    if agency is None:
        abort(403)
    return render_template(
        "gestion_asesores.html",
        agencia=dict(agency),
        asesores=advisors,
        nombre=session.get("nombre", ""),
        es_admin=True,
        route="gestion-asesores",
    )


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
                FROM usuarios WHERE rol = 'asesor' AND agencia_id = ?
                ORDER BY LOWER(nombre_completo), id
                """,
                (_session_agency_id(),),
            )
        ]
        prepaga_options = [
            row["prepaga"]
            for row in connection.execute(
                "SELECT DISTINCT prepaga, LOWER(prepaga) AS prepaga_sort FROM fichas "
                "WHERE agencia_id = ? AND prepaga IS NOT NULL AND prepaga != '' "
                "ORDER BY prepaga_sort",
                (_session_agency_id(),),
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
              AND agencia_id = ?
            UNION
            SELECT periodo FROM cierres_periodo WHERE agencia_id = ?
            UNION
            SELECT periodo FROM cierres_prepaga WHERE agencia_id = ?
            ORDER BY periodo DESC
            """,
            (_session_agency_id(), _session_agency_id(), _session_agency_id()),
        ).fetchall()
        active_periods = {
            brand: _active_period(connection, brand, _session_agency_id())
            for brand in prepaga_options
        }
        active_period = _active_period(
            connection, agency_id=_session_agency_id()
        )
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
            """
            SELECT periodo, prepaga, periodo_cierre_id FROM fichas
            WHERE id = ? AND agencia_id = ?
            """,
            (ficha_id, _session_agency_id()),
        ).fetchone()
        if ficha is None:
            abort(404)
        if ficha["periodo_cierre_id"] is not None:
            flash("No se puede modificar una ficha de un período cerrado.", "warning")
            return redirect(url_for("admin_dashboard", **request.args.to_dict()))
        closed = connection.execute(
            """
            SELECT 1 FROM cierres_periodo WHERE periodo = ?
              AND agencia_id = ?
            UNION ALL
            SELECT 1 FROM cierres_prepaga
            WHERE periodo = ? AND prepaga = ? AND agencia_id = ?
            LIMIT 1
            """,
            (
                ficha["periodo"], _session_agency_id(),
                ficha["periodo"], ficha["prepaga"], _session_agency_id(),
            ),
        ).fetchone()
        if closed:
            flash("No se puede modificar una ficha de un período cerrado.", "warning")
        else:
            connection.execute(
                "UPDATE fichas SET estado = ? WHERE id = ? AND agencia_id = ?",
                (state, ficha_id, _session_agency_id()),
            )
            flash(f"Ficha {state.lower()} correctamente.", "success")
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
    agency_id = _session_agency_id()
    with db_connection() as connection:
        requested_prepaga = request.form.get("prepaga", "").strip()
        requested_period = request.form.get("periodo", "").strip()
        if requested_prepaga:
            if not requested_period or not PERIOD_RE.fullmatch(requested_period):
                abort(400, description="El período a cerrar no es válido.")
            active_period = _active_period(
                connection, requested_prepaga, agency_id
            )
            if requested_period != active_period:
                abort(400, description="Solo se puede cerrar el período activo de esa prepaga.")
            existing = connection.execute(
                "SELECT 1 FROM cierres_prepaga "
                "WHERE periodo = ? AND prepaga = ? AND agencia_id = ?",
                (requested_period, requested_prepaga, agency_id),
            ).fetchone()
            if existing:
                abort(409, description="El período de esa prepaga ya está cerrado.")
            period_id = _ensure_period_record(
                connection, requested_period, agency_id=agency_id
            )
            connection.execute(
                """
                INSERT INTO cierres_prepaga (
                    periodo, agencia_id, prepaga, cerrado_por
                ) VALUES (?, ?, ?, ?)
                """,
                (
                    requested_period, agency_id, requested_prepaga,
                    session["user_id"],
                ),
            )
            _snapshot_closed_fichas(
                connection,
                period_id,
                "periodo = ? AND prepaga = ? AND agencia_id = ?",
                (requested_period, requested_prepaga, agency_id),
            )
            connection.execute(
                """
                UPDATE periodos_cierre
                SET fecha_cierre = CURRENT_TIMESTAMP, usuario_cierre_id = ?
                WHERE id = ? AND agencia_id = ?
                """,
                (session["user_id"], period_id, agency_id),
            )
            next_period = _month_after(requested_period)
            flash(
                f"Período {requested_period} de {requested_prepaga} cerrado. "
                f"El nuevo período activo para esa prepaga es {next_period}.",
                "success",
            )
            redirect_args = {
                "periodo": "activo",
                "asesor_id": request.form.get("asesor_id", "todos"),
                "prepaga": request.form.get("filtro_prepaga", ""),
                "q": request.form.get("q", ""),
            }
            return redirect(url_for("admin_dashboard", **redirect_args))

        active_period = _active_period(connection, agency_id=agency_id)
        requested_period = requested_period or active_period
        if not PERIOD_RE.fullmatch(requested_period):
            abort(400, description="El período a cerrar no es válido.")
        if requested_period != active_period:
            abort(400, description="Solo se puede cerrar el período activo.")
        period_id = _ensure_period_record(connection, requested_period)
        brands = [
            row["prepaga"]
            for row in connection.execute(
                "SELECT DISTINCT prepaga FROM fichas "
                "WHERE agencia_id = ? AND prepaga IS NOT NULL AND prepaga != ''",
                (agency_id,),
            )
        ]
        for brand in brands:
            brand_period = _active_period(connection, brand, agency_id)
            existing_brand_close = connection.execute(
                "SELECT 1 FROM cierres_prepaga "
                "WHERE periodo = ? AND prepaga = ? AND agencia_id = ?",
                (brand_period, brand, agency_id),
            ).fetchone()
            if existing_brand_close is None:
                connection.execute(
                    """
                    INSERT INTO cierres_prepaga (
                        periodo, agencia_id, prepaga, cerrado_por
                    ) VALUES (?, ?, ?, ?)
                    """,
                    (brand_period, agency_id, brand, session["user_id"]),
                )
            _snapshot_closed_fichas(
                connection,
                period_id,
                "periodo = ? AND prepaga = ? AND agencia_id = ?",
                (brand_period, brand, agency_id),
            )
        connection.execute(
            """
            INSERT INTO cierres_periodo (periodo, agencia_id, cerrado_por)
            VALUES (?, ?, ?)
            ON CONFLICT (agencia_id, periodo) DO NOTHING
            """,
            (requested_period, agency_id, session["user_id"]),
        )
        connection.execute(
            """
            UPDATE periodos_cierre
            SET estado = 'cerrado', fecha_cierre = CURRENT_TIMESTAMP,
                usuario_cierre_id = ?
            WHERE id = ? AND agencia_id = ?
            """,
            (session["user_id"], period_id, agency_id),
        )
        next_active_period = _active_period(connection, agency_id=agency_id)
        _ensure_period_record(
            connection, next_active_period, agency_id=agency_id
        )
        flash("Período activo cerrado para todas las prepagas.", "success")
    return redirect(url_for("admin_dashboard", periodo="activo"))


def _selected_fichas_for_export() -> list[dict[str, Any]]:
    clauses, values, period, prepaga, _, selected_advisor_id = _dashboard_filters()
    with db_connection() as connection:
        if selected_advisor_id:
            advisor = connection.execute(
                "SELECT 1 FROM usuarios WHERE id = ? AND rol = 'asesor' "
                "AND agencia_id = ?",
                (int(selected_advisor_id), _session_agency_id()),
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


def _csv_safe_cell(value: Any) -> Any:
    if isinstance(value, str) and value.startswith(("=", "+", "-", "@")):
        return "'" + value
    return value


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
            _csv_safe_cell(value)
            for value in [
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
    agency_id = _session_agency_id()
    with db_connection() as connection:
        brands = [
            row["prepaga"]
            for row in connection.execute(
                """
                SELECT DISTINCT prepaga, LOWER(prepaga) AS prepaga_sort
                FROM fichas
                WHERE asesor_id = ? AND agencia_id = ?
                  AND prepaga IS NOT NULL AND prepaga != ''
                ORDER BY prepaga_sort
                """,
                (advisor_id, agency_id),
            )
        ]
        summaries: list[dict[str, Any]] = []
        grand_total = Decimal(0)
        for brand in brands:
            active_period = _active_period(connection, brand, agency_id)
            totals = connection.execute(
                """
                SELECT COUNT(*) AS fichas_total,
                       SUM(CASE WHEN estado = 'APROBADA' THEN 1 ELSE 0 END)
                           AS fichas_aprobadas,
                       SUM(CASE WHEN estado = 'APROBADA'
                                THEN COALESCE(importe_comision, 0) ELSE 0 END)
                           AS importe_a_liquidar
                FROM fichas
                WHERE asesor_id = ? AND agencia_id = ?
                  AND prepaga = ? AND periodo = ?
                """,
                (advisor_id, agency_id, brand, active_period),
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
        active_ficha_periods = [
            (brand, _active_period(connection, brand, agency_id))
            for brand in brands
        ]
        active_ficha_filter = " OR ".join(
            "(f.prepaga = ? AND f.periodo = ?)" for _ in active_ficha_periods
        ) or "1 = 0"
        fichas = connection.execute(
            f"""
            SELECT f.*, u.nombre_completo
            FROM fichas AS f
            LEFT JOIN usuarios AS u ON u.id = f.asesor_id
            WHERE f.asesor_id = ? AND f.agencia_id = ?
              AND ({active_ficha_filter})
            ORDER BY f.fecha_carga DESC, f.id DESC
            """,
            (
                advisor_id,
                agency_id,
                *[
                    value
                    for active_period in active_ficha_periods
                    for value in active_period
                ],
            ),
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


@app.get("/historial-liquidaciones")
@login_required
def historial_liquidaciones() -> Any:
    role = session.get("rol")
    if role not in {"admin", "asesor"}:
        abort(403)
    selected_period_id = request.args.get("periodo_id", "").strip()
    selected_advisor_id = request.args.get("asesor_id", "").strip()
    prepaga = request.args.get("prepaga", "").strip()
    if role == "asesor":
        advisor_id = int(session["user_id"])
        selected_advisor_id = str(advisor_id)
    elif selected_advisor_id:
        if not selected_advisor_id.isdigit() or int(selected_advisor_id) < 1:
            abort(400, description="El asesor seleccionado no es válido.")
        advisor_id = int(selected_advisor_id)
    else:
        advisor_id = None

    with db_connection() as connection:
        periods = [
            dict(row)
            for row in connection.execute(
                """
                SELECT id, nombre_periodo, fecha_cierre
                FROM periodos_cierre
                WHERE agencia_id = ?
                  AND (
                    estado = 'cerrado'
                   OR EXISTS (
                        SELECT 1 FROM cierres_prepaga
                        WHERE cierres_prepaga.periodo =
                              periodos_cierre.nombre_periodo
                          AND cierres_prepaga.agencia_id =
                              periodos_cierre.agencia_id
                   )
                  )
                ORDER BY nombre_periodo DESC
                """,
                (_session_agency_id(),),
            )
        ]
        advisors = (
            [
                dict(row)
                for row in connection.execute(
                    """
                    SELECT id, username, nombre_completo FROM usuarios
                    WHERE rol = 'asesor' AND agencia_id = ?
                    ORDER BY LOWER(nombre_completo), id
                    """,
                    (_session_agency_id(),),
                )
            ]
            if role == "admin"
            else []
        )
        selected_period = None
        fichas: list[dict[str, Any]] = []
        total_liquidado = Decimal(0)
        total_comision = Decimal(0)
        prepaga_options: list[str] = []
        if selected_period_id:
            if not selected_period_id.isdigit() or int(selected_period_id) < 1:
                abort(400, description="El período seleccionado no es válido.")
            selected_period = next(
                (
                    period
                    for period in periods
                    if int(period["id"]) == int(selected_period_id)
                ),
                None,
            )
            if selected_period is None:
                abort(404, description="El período cerrado no existe.")
            clauses = ["f.periodo_cierre_id = ?", "f.agencia_id = ?"]
            values: list[Any] = [
                int(selected_period_id), _session_agency_id()
            ]
            if advisor_id is not None:
                clauses.append("f.asesor_id = ?")
                values.append(advisor_id)
            if prepaga:
                clauses.append("f.prepaga = ?")
                values.append(prepaga)
            where_clause, query_values = _query_filters(clauses, values)
            rows = connection.execute(
                f"""
                SELECT f.*, u.nombre_completo
                FROM fichas AS f
                LEFT JOIN usuarios AS u ON u.id = f.asesor_id
                {where_clause}
                ORDER BY LOWER(f.prepaga), f.fecha_carga DESC, f.id DESC
                """,
                query_values,
            ).fetchall()
            fichas = [_dict_ficha(row) for row in rows]
            totals = connection.execute(
                f"""
                SELECT SUM(COALESCE(f.comision_liquidada_cierre, 0)) AS liquidado,
                       SUM(COALESCE(f.importe_comision_cierre, 0)) AS comision
                FROM fichas AS f
                {where_clause}
                """,
                query_values,
            ).fetchone()
            total_liquidado = Decimal(str(totals["liquidado"] or 0))
            total_comision = Decimal(str(totals["comision"] or 0))
            brand_clauses = ["periodo_cierre_id = ?", "agencia_id = ?"]
            brand_values: list[Any] = [
                int(selected_period_id), _session_agency_id()
            ]
            if advisor_id is not None:
                brand_clauses.append("asesor_id = ?")
                brand_values.append(advisor_id)
            brand_where, brand_query_values = _query_filters(
                brand_clauses, brand_values
            )
            prepaga_options = [
                row["prepaga"]
                for row in connection.execute(
                    f"""
                    SELECT DISTINCT prepaga FROM fichas {brand_where}
                    ORDER BY LOWER(prepaga)
                    """,
                    brand_query_values,
                )
                if row["prepaga"]
            ]
    return render_template(
        "historial_liquidaciones.html",
        periodos=periods,
        periodo_seleccionado=selected_period,
        periodo_id_actual=selected_period_id,
        asesores=advisors,
        asesor_id_actual=selected_advisor_id,
        prepagas=prepaga_options,
        prepaga_actual=prepaga,
        fichas=fichas,
        total_liquidado=total_liquidado,
        total_comision=total_comision,
        es_admin=role == "admin",
        nombre=session.get("nombre", ""),
        route="historial-liquidaciones",
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
    with db_connection() as connection:
        prepagas = connection.execute(
            """
            SELECT pc.prepaga, pc.porcentaje_comision
            FROM prepagas_config AS pc
            JOIN usuarios AS owner ON owner.id = pc.usuario_id
            WHERE owner.agencia_id = ? AND owner.rol = 'admin'
              AND pc.agencia_id = ? AND pc.activa = TRUE
            ORDER BY LOWER(prepaga)
            """,
            (_session_agency_id(), _session_agency_id()),
        ).fetchall()
    return render_template(
        "cargar_ficha.html",
        nombre=session.get("nombre", ""),
        prepagas=prepagas,
        es_admin=False,
        route="cargar-ficha",
    )


def _parse_amount(
    raw_value: str, amount_name: str = "importe de comisión"
) -> Decimal:
    cleaned = raw_value.strip().replace("$", "").replace(" ", "")
    if "," in cleaned:
        cleaned = cleaned.replace(".", "").replace(",", ".")
    try:
        amount = Decimal(cleaned)
    except InvalidOperation as exc:
        raise ValueError(f"El {amount_name} no es válido.") from exc
    if not amount.is_finite() or amount < 0:
        raise ValueError(f"El {amount_name} debe ser un valor no negativo.")
    return amount


def _parse_percentage(raw_value: str) -> int:
    cleaned = raw_value.strip()
    if not re.fullmatch(r"\d+", cleaned):
        raise ValueError("El porcentaje de comisión debe ser un número entero.")
    return int(cleaned)


@app.route("/configuracion-prepagas", methods=["GET", "POST"])
@login_required
def configuracion_prepagas() -> Any:
    denied_response = _require_prepaga_config_admin()
    if denied_response is not None:
        return denied_response

    user_id = int(session["user_id"])
    agency_id = _session_agency_id()
    if request.method == "POST":
        prepaga = request.form.get("prepaga", "").strip()
        try:
            if not prepaga:
                raise ValueError("El nombre de la prepaga es obligatorio.")
            percentage = _parse_percentage(
                request.form.get("porcentaje_comision", "")
            )
            with db_connection() as connection:
                existing = connection.execute(
                    """
                    SELECT id FROM prepagas_config
                    WHERE usuario_id = ? AND agencia_id = ?
                      AND LOWER(prepaga) = LOWER(?)
                    """,
                    (user_id, agency_id, prepaga),
                ).fetchone()
                if existing is not None:
                    raise ValueError("Ya tienes esa prepaga configurada.")
                connection.execute(
                    """
                    INSERT INTO prepagas_config (
                        usuario_id, prepaga, porcentaje_comision, activa,
                        agencia_id
                    ) VALUES (?, ?, ?, TRUE, ?)
                    """,
                    (user_id, prepaga, percentage, agency_id),
                )
            flash("Prepaga agregada correctamente.", "success")
        except ValueError as exc:
            flash(str(exc), "error")
        return redirect(url_for("configuracion_prepagas"))

    with db_connection() as connection:
        prepagas = connection.execute(
            """
            SELECT id, prepaga, porcentaje_comision, activa
            FROM prepagas_config
            WHERE usuario_id = ? AND agencia_id = ?
            ORDER BY LOWER(prepaga)
            """,
            (user_id, agency_id),
        ).fetchall()
    return render_template(
        "configuracion_prepagas.html",
        nombre=session.get("nombre", ""),
        prepagas=prepagas,
        es_admin=True,
        route="configuracion-prepagas",
    )


@app.post("/configuracion-prepagas/<int:config_id>/porcentaje")
@login_required
def actualizar_porcentaje_prepaga(config_id: int) -> Any:
    denied_response = _require_prepaga_config_admin()
    if denied_response is not None:
        return denied_response
    try:
        percentage = _parse_percentage(
            request.form.get("porcentaje_comision", "")
        )
        with db_connection() as connection:
            result = connection.execute(
                """
                UPDATE prepagas_config
                SET porcentaje_comision = ?
                WHERE id = ? AND usuario_id = ? AND agencia_id = ?
                """,
                (
                    percentage, config_id, session["user_id"],
                    _session_agency_id(),
                ),
            )
            if result.rowcount == 0:
                abort(404)
        flash("Porcentaje actualizado correctamente.", "success")
    except ValueError as exc:
        flash(str(exc), "error")
    return redirect(url_for("configuracion_prepagas"))


@app.post("/configuracion-prepagas/<int:config_id>/alternar")
@login_required
def alternar_prepaga(config_id: int) -> Any:
    denied_response = _require_prepaga_config_admin()
    if denied_response is not None:
        return denied_response
    with db_connection() as connection:
        result = connection.execute(
            """
            UPDATE prepagas_config
            SET activa = CASE WHEN activa THEN FALSE ELSE TRUE END
            WHERE id = ? AND usuario_id = ? AND agencia_id = ?
            """,
            (config_id, session["user_id"], _session_agency_id()),
        )
        if result.rowcount == 0:
            abort(404)
    flash("Estado de la prepaga actualizado.", "success")
    return redirect(url_for("configuracion_prepagas"))


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
    empresa = (request.form.get("empresa") or "").strip()
    telefono = (request.form.get("telefono") or "").strip()
    grupo_familiar = request.form.get("grupo_familiar") or "Sin especificar"
    raw_salary = request.form.get("sueldo_bruto", "")
    raw_contribution = request.form.get("aporte", "")
    try:
        if not client_name or not cuil or not prepaga:
            raise ValueError("Nombre, CUIL y prepaga son obligatorios.")
        salary = _parse_amount(raw_salary, "sueldo bruto")
        contribution = _parse_amount(raw_contribution, "aporte")
        active_period = date.today().strftime("%Y-%m")
        with db_connection() as connection:
            agency_id = _session_agency_id()
            configured_prepaga = connection.execute(
                """
                SELECT pc.porcentaje_comision
                FROM prepagas_config AS pc
                JOIN usuarios AS owner ON owner.id = pc.usuario_id
                WHERE owner.agencia_id = ? AND owner.rol = 'admin'
                  AND pc.agencia_id = ? AND pc.prepaga = ? AND pc.activa = TRUE
                ORDER BY owner.id
                LIMIT 1
                """,
                (agency_id, agency_id, prepaga),
            ).fetchone()
            if configured_prepaga is None:
                raise ValueError(
                    "La prepaga seleccionada no está activa en tu configuración."
                )
            percentage = Decimal(str(configured_prepaga["porcentaje_comision"]))
            commission = contribution * percentage / Decimal("100")
            active_period = _active_period(connection, agency_id=agency_id)
            connection.execute(
                """
                INSERT INTO fichas (
                    asesor_id, cliente_nombre, cuil, prepaga, plan,
                    importe_comision, estado, periodo, fecha_carga,
                    nombre_afiliado, cuil_afiliado, empresa, telefono,
                    grupo_familiar, sueldo_bruto, aporte,
                    porcentaje_comision, agencia_id, fecha_creacion
                ) VALUES (?, ?, ?, ?, ?, ?, 'PENDIENTE', ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
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
                    empresa,
                    telefono,
                    grupo_familiar,
                    float(salary),
                    float(contribution),
                    float(percentage),
                    agency_id,
                    datetime.now().isoformat(timespec="seconds"),
                ),
            )
        flash("Ficha cargada correctamente.", "success")
        return redirect(url_for("mis_fichas"))
    except ValueError as exc:
        flash(str(exc), "error")
        return redirect(url_for("cargar_ficha"))


@app.cli.command("limpiar-db-pruebas")
@click.option(
    "--confirmar",
    is_flag=True,
    help="Confirma el borrado de fichas y el restablecimiento de todas las claves.",
)
def limpiar_db_pruebas(confirmar: bool) -> None:
    """Limpia datos de prueba y restablece las cuentas a la clave temporal configurada."""
    reset_password = os.environ.get("RESET_PASSWORD")
    if not reset_password:
        raise click.ClickException(
            "Falta definir la variable de entorno RESET_PASSWORD para restablecer "
            "las contraseñas."
        )
    if not confirmar:
        raise click.ClickException(
            "Operación cancelada. Vuelve a ejecutar con --confirmar para "
            "borrar las fichas y restablecer la contraseña temporal de todos."
        )

    with db_connection() as connection:
        user_columns = _columns(connection, "usuarios")
        users = connection.execute("SELECT id FROM usuarios ORDER BY id").fetchall()
        for user in users:
            password_hash = generate_password_hash(reset_password)
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