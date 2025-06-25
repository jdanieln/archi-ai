#!/usr/bin/env python3
import os
import sys
import json
import subprocess
import tempfile
from pathlib import Path

from dotenv import load_dotenv
import openai

# ──────────────────────────────────────────────────────────
# 0) Carga del .env
# ──────────────────────────────────────────────────────────
ROOT = Path(__file__).resolve().parents[2]   # .../archi-ai/python
ENV  = ROOT / ".env"
if not ENV.is_file():
    raise FileNotFoundError(f"No encontré el archivo de configuración {ENV}")
load_dotenv(dotenv_path=ENV)

# ──────────────────────────────────────────────────────────
# 1) Configuración de OpenAI
# ──────────────────────────────────────────────────────────
openai.api_key = os.getenv("OPENAI_API_KEY")
if not openai.api_key:
    raise RuntimeError("La variable OPENAI_API_KEY no está definida en python/.env")

# ──────────────────────────────────────────────────────────
# 2) Extracción LLM (antes en extract.py)
# ──────────────────────────────────────────────────────────
_PROMPT_TEMPLATE = """
Toma estas historias de usuario y extrae servicios, operaciones y parámetros.
Devuélvelo SOLO como JSON con estructura:
{
  "services": [
    { "name": "...", "operations": [ { "name": "...", "params": ["..."] }, ... ] },
    ...
  ],
  "calls": [ { "from": "...", "to": "..." }, ... ]
}
Historias:
%%STORIES%%
"""

def extract(gen_stories: str) -> dict:
    prompt = _PROMPT_TEMPLATE.replace("%%STORIES%%", gen_stories)
    resp = openai.chat.completions.create(
        model="gpt-4",
        messages=[{"role": "user", "content": prompt}],
        temperature=0
    )
    return json.loads(resp.choices[0].message.content)

# ──────────────────────────────────────────────────────────
# 3) Importa las métricas desde metrics.py
# ──────────────────────────────────────────────────────────
from .metrics import lcom, sgm, noo, coupling_out, sgm_sd

# ──────────────────────────────────────────────────────────
# 4) Directorio de historias de usuario
# ──────────────────────────────────────────────────────────
USER_STORIES_DIR = ROOT / "../" / "data" / "user-stories-datasets"

# ──────────────────────────────────────────────────────────
# 5) Procesamiento de cada archivo
# ──────────────────────────────────────────────────────────
def process_file(path: Path):
    print(f"\n=== Procesando {path.name} ===")
    text     = path.read_text(encoding="utf-8")
    genotype = extract(text)
    calls    = genotype.get("calls", [])

    # --- 5.1: Validación Lean ---
    # vuelca el genotipo a JSON temporal dentro de lean/
    lean_dir = ROOT / "lean"
    tmp = tempfile.NamedTemporaryFile(
        mode="w", suffix=".json", delete=False, dir=lean_dir
    )
    json.dump(genotype, tmp)
    tmp.flush()
    tmp.close()

    # invoca el verificador Lean
    res = subprocess.run(
        ["lake", "run", "verifyGenotype", tmp.name],
        cwd=str(lean_dir),
        capture_output=True,
        text=True
    )
    if res.returncode != 0:
        print(f"❌ Genotipo rechazado por Lean: {res.stderr.strip()}", file=sys.stderr)
        return  # aborta este archivo y pasa al siguiente

    # --- 5.2: Cálculo e impresión de métricas ---
    for svc in genotype.get("services", []):
        name = svc["name"]
        ops  = svc.get("operations", [])
        co   = coupling_out(name, calls)
        sd   = sgm_sd(ops)
        print(
            f"* {name}: "
            f"LCOM={lcom(ops):.2f}, "
            f"SGM={sgm(ops):.2f}, "
            f"SGM-σ={sd:.2f}, "
            f"NOO={noo(ops)}, "
            f"CouplingOut={co}"
        )

    for c in calls:
        print(f"    Llamada RPC: {c['from']} → {c['to']}")

def main():
    if not USER_STORIES_DIR.exists():
        print(f"ERROR: No existe {USER_STORIES_DIR}", file=sys.stderr)
        sys.exit(1)

    txts = sorted(USER_STORIES_DIR.glob("*.txt"))
    if not txts:
        print(f"ERROR: No hay archivos .txt en {USER_STORIES_DIR}", file=sys.stderr)
        sys.exit(1)

    for txt in txts:
        process_file(txt)

if __name__ == "__main__":
    main()
