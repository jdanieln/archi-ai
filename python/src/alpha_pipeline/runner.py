#!/usr/bin/env python3
import os
import sys
import json
import subprocess
import tempfile
from pathlib import Path

# Las librerías de terceros que usas
from dotenv import load_dotenv
import openai

# ──────────────────────────────────────────────────────────
# 0) Carga del .env y Definición de Rutas
# ──────────────────────────────────────────────────────────
# Esta es la parte clave que ajustamos a tu estructura
PYTHON_ROOT = Path(__file__).resolve().parents[2]  # Navega hasta la carpeta 'python'
ENV_PATH = PYTHON_ROOT / ".env"
LEAN_PROJECT_DIR = PYTHON_ROOT / "formal"          # La carpeta de tu proyecto Lean
USER_STORIES_DIR = PYTHON_ROOT.parent / "data" / "user-stories-datasets" # Sube un nivel a ARCHI-AI y luego a data

if not ENV_PATH.is_file():
    raise FileNotFoundError(f"No encontré el archivo de configuración {ENV_PATH}")
load_dotenv(dotenv_path=ENV_PATH)

# ──────────────────────────────────────────────────────────
# 1) Configuración de OpenAI (Sin cambios)
# ──────────────────────────────────────────────────────────
openai.api_key = os.getenv("OPENAI_API_KEY")
if not openai.api_key:
    raise RuntimeError("La variable OPENAI_API_KEY no está definida en python/.env")

# ──────────────────────────────────────────────────────────
# 2) Extracción LLM (Sin cambios)
# ──────────────────────────────────────────────────────────
_PROMPT_TEMPLATE = """
Toma estas historias de usuario y extrae servicios, operaciones y parámetros.
Devuélvelo SOLO como JSON con estructura:
{
  "services": [
    { "name": "...", "operations": [ { "name": "...", "params": ["..."] }, ... ] },
    ...
  ],
  "calls": [ { "caller": "...", "callee": "..." }, ... ]
}
Historias:
%%STORIES%%
"""
# NOTA: Asegúrate de que tu prompt de OpenAI use "caller" y "callee"
# para que coincida con las estructuras de Lean.

def extract(gen_stories: str) -> dict:
    prompt = _PROMPT_TEMPLATE.replace("%%STORIES%%", gen_stories)
    resp = openai.chat.completions.create(
        model="gpt-4",
        messages=[{"role": "user", "content": prompt}],
        temperature=0
    )
    return json.loads(resp.choices[0].message.content)

# ──────────────────────────────────────────────────────────
# 3) Procesamiento de cada archivo (Lógica de Integración)
# ──────────────────────────────────────────────────────────
def process_file(path: Path):
    print(f"\n=== Procesando {path.name} ===")
    try:
        text = path.read_text(encoding="utf-8")
        genotype = extract(text)
    except Exception as e:
        print(f"❌ Error durante la extracción de OpenAI: {e}", file=sys.stderr)
        return

    # --- 3.1: Validación con Lean ---
    # Usamos un archivo temporal para pasar el genotipo a Lean.
    # Es la forma más robusta y segura.
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".json", delete=False, dir=LEAN_PROJECT_DIR, encoding="utf-8"
    ) as tmp:
        json.dump(genotype, tmp)
        temp_file_path = tmp.name

    try:
        # Invoca el verificador Lean pasándole la RUTA al archivo JSON temporal.
        # NOTA: El nombre del ejecutable es "validate" (como en el lakefile.lean).
        res = subprocess.run(
            ["lake", "exe", "validate", temp_file_path],
            cwd=str(LEAN_PROJECT_DIR), # Ejecuta el comando desde la carpeta del proyecto Lean
            capture_output=True,
            text=True,
            encoding="utf-8"
        )

        # Analiza el resultado de Lean
        lean_output = res.stdout.strip()

        if lean_output == "OK":
            print("✅ Genotipo aceptado por Lean.")
        else:
            # Si la salida no es "OK", es porque Lean encontró un error.
            error_message = lean_output if lean_output else res.stderr.strip()
            print(f"❌ Genotipo rechazado por Lean: {error_message}", file=sys.stderr)

    finally:
        # Asegúrate de limpiar el archivo temporal después de usarlo
        os.remove(temp_file_path)

# ──────────────────────────────────────────────────────────
# 4) Función Principal
# ──────────────────────────────────────────────────────────
def main():
    if not USER_STORIES_DIR.exists():
        print(f"ERROR: No existe {USER_STORIES_DIR}", file=sys.stderr)
        sys.exit(1)

    txts = sorted(USER_STORIES_DIR.glob("*.txt"))
    if not txts:
        print(f"ERROR: No hay archivos .txt en {USER_STORIES_DIR}", file=sys.stderr)
        sys.exit(1)

    # Primero, asegúrate de que el proyecto Lean esté construido
    print("Construyendo el proyecto Lean (si es necesario)...")
    build_res = subprocess.run(["lake", "build"], cwd=str(LEAN_PROJECT_DIR), capture_output=True, text=True)
    if build_res.returncode != 0:
        print("❌ ERROR: Falló la compilación de Lean. Abortando.", file=sys.stderr)
        print(build_res.stderr, file=sys.stderr)
        sys.exit(1)
    print("Proyecto Lean construido exitosamente.")

    for txt in txts:
        process_file(txt)

if __name__ == "__main__":
    main()