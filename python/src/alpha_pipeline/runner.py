#!/usr/bin/env python3
import os
import sys
import json
import csv
import random
import time
import tempfile
import subprocess
from copy import deepcopy
from datetime import datetime
from pathlib import Path

from dotenv import load_dotenv
import openai

# ──────────────────────────────────────────────────────────
# 0) Configuración de rutas y .env
# ──────────────────────────────────────────────────────────
PYTHON_ROOT       = Path(__file__).resolve().parents[2]
ENV_PATH          = PYTHON_ROOT / ".env"
LEAN_PROJECT_DIR  = PYTHON_ROOT / "formal"
USER_STORIES_DIR  = PYTHON_ROOT.parent / "data" / "user-stories-datasets"
EXPERIMENT_DIR    = PYTHON_ROOT / "experiments"
DB_FILE           = EXPERIMENT_DIR / "program_db.jsonl"

EXPERIMENT_DIR.mkdir(exist_ok=True)

if not ENV_PATH.is_file():
    raise FileNotFoundError(f"No encontré {ENV_PATH}")
load_dotenv(dotenv_path=ENV_PATH)

# ──────────────────────────────────────────────────────────
# 1) API Key de OpenAI
# ──────────────────────────────────────────────────────────
openai.api_key = os.getenv("OPENAI_API_KEY")
if not openai.api_key:
    raise RuntimeError("OPENAI_API_KEY no está definido en .env")

# ──────────────────────────────────────────────────────────
# 2) Parámetros evolutivos y modelos
# ──────────────────────────────────────────────────────────
POP_SIZE        = 10
GENERATIONS     = 5
ELITE           = 5
MUT_RATE        = 0.2
N_INSPIRATIONS  = 3
TEMP_OPTIONS    = [0.5]
MODELS          = ["gpt-4o-mini"]

# ──────────────────────────────────────────────────────────
# 3) Plantillas de prompt (microservicios)
# ──────────────────────────────────────────────────────────
_SIMPLE_PROMPT = """
Analiza las siguientes historias de usuario y descubre microservicios, operaciones y sus parámetros.

Devuelve SOLO un objeto JSON con la siguiente estructura EXACTA:

{{
  "microservices": [
    {{
      "name": "UserManagement",
      "ops": [
        {{ "name": "RegisterUser", "params": ["username", "email"] }},
        {{ "name": "Login",        "params": ["username", "password"] }}
      ]
    }}
    // ...
  ],
  "calls": [
    {{ "caller": "UserManagement", "callee": "Notification" }}
    // ...
  ]
}}

NO agregues ninguna explicación, comentario, ni texto fuera de las llaves JSON.

Historias de usuario:
{stories}
"""

_INSPIRATION_PROMPT = """
Prompt Sampler AlphaEvolve:
1) Contexto – Historias de usuario:
{stories}

2) Genotipo padre (ejemplo válido):
{parent}

3) Inspiraciones (otros ejemplos válidos, hasta {n_insp}):
{inspirations}

Definición de microservicio:
- Debe tener una sola responsabilidad (1–5 operaciones como máximo).
- Ser independiente y débilmente acoplado.
- Tener un bounded context claro.

Salida esperada (SOLO JSON):
{{
  "microservices": [
    {{
      "name": "...",
      "ops": [
        {{ "name": "...", "params": ["..."] }},
        …
      ]
    }},
    …
  ],
  "calls": [
    {{ "caller": "...", "callee": "..." }},
    …
  ]
}}

**NO** agregues texto antes ni después del objeto JSON.
"""

def build_prompt(stories: str,
                 parent: dict | None = None,
                 inspirations: list[dict] | None = None) -> str:
    inspirations = inspirations or []
    insp_str = "\n\n".join(
        json.dumps(i, ensure_ascii=False) for i in inspirations[:N_INSPIRATIONS]
    )
    if parent is not None:
        return _INSPIRATION_PROMPT.format(
            stories=stories,
            parent=json.dumps(parent, ensure_ascii=False),
            inspirations=insp_str,
            n_insp=N_INSPIRATIONS
        )
    else:
        return _SIMPLE_PROMPT.format(stories=stories)

# ──────────────────────────────────────────────────────────
# 4) Helpers de DB de programas
# ──────────────────────────────────────────────────────────
def save_to_db(record: dict):
    with open(DB_FILE, "a", encoding="utf-8") as f:
        f.write(json.dumps(record, ensure_ascii=False) + "\n")

def load_best_n(n: int) -> list[dict]:
    if not DB_FILE.exists():
        return []
    recs = [json.loads(line) for line in DB_FILE.read_text(encoding="utf-8").splitlines()]
    recs.sort(key=lambda r: r["fitness"])
    return [r["genotype"] for r in recs[:n]]

# ──────────────────────────────────────────────────────────
# 5) LLM ensemble + Prompt Sampling
# ──────────────────────────────────────────────────────────
def extract_prompt_ensemble(stories: str,
                            temperature: float,
                            parent: dict=None,
                            inspirations: list[dict]=None
                            ) -> tuple[str, dict]:
    prompt     = build_prompt(stories, parent, inspirations)
    candidates = []
    last_model = MODELS[0]
    last_gt    = {}

    for model in MODELS:
        last_model = model
        try:
            resp = openai.chat.completions.create(
                model=model,
                messages=[{"role": "user", "content": prompt}],
                temperature=temperature
            )
            text = resp.choices[0].message.content
        except Exception as e:
            print(f"[WARN] fallo API con {model}: {e}", file=sys.stderr)
            continue

        try:
            gt = json.loads(text)
        except json.JSONDecodeError:
            gt = {"_raw": text}

        candidates.append((model, gt))
        last_gt = gt

    for model, gt in candidates:
        valid, _, _ = lean_evaluate(gt)
        if valid:
            return model, gt

    if candidates:
        return candidates[-1]
    return last_model, last_gt

# ──────────────────────────────────────────────────────────
# 6) Validación & métricas en Lean
# ──────────────────────────────────────────────────────────
def lean_evaluate(genotype: dict) -> (bool, str, dict):
    with tempfile.NamedTemporaryFile(
            mode="w", suffix=".json", delete=False,
            dir=LEAN_PROJECT_DIR, encoding="utf-8"
    ) as tmp:
        json.dump(genotype, tmp, ensure_ascii=False)
        path = tmp.name

    try:
        res = subprocess.run(
            f'lake exe validate "{path}"',
            cwd=str(LEAN_PROJECT_DIR),
            shell=True, capture_output=True, text=True
        )
        try:
            data = json.loads(res.stdout)
        except Exception:
            data = {}
        return (
            data.get("status") == "OK",
            data.get("message", ""),
            data.get("metrics", {})
        )
    finally:
        os.remove(path)

# ──────────────────────────────────────────────────────────
# 7) Clase Individual + operadores genéticos
# ──────────────────────────────────────────────────────────
class Individual:
    def __init__(self, story_name: str, stories: str,
                 temp: float, gen_id: int, ind_id: int,
                 parent: dict=None, inspirations: list[dict]=None):
        self.story_name    = story_name
        self.stories       = stories
        self.temperature   = temp
        self.gen_id        = gen_id
        self.indiv_id      = ind_id
        self.parent        = parent
        self.inspirations  = inspirations or []
        self.model         = None
        self.genotype      = None
        self.valid         = False
        self.validation    = ""
        self.metrics       = {}
        self.fitness       = float("inf")

    def evaluate(self):
        global_insp = load_best_n(N_INSPIRATIONS)
        insp = (self.inspirations or []) + global_insp

        start_llm = time.time()
        model, geno = extract_prompt_ensemble(
            self.stories, self.temperature, self.parent, insp
        )
        self.metrics["time_llm"] = round(time.time() - start_llm, 2)
        self.model = model
        self.genotype = geno

        start_lean = time.time()
        self.valid, self.validation, metrics = lean_evaluate(self.genotype)
        self.metrics["time_lean"] = round(time.time() - start_lean, 2)
        self.metrics.update(metrics)

        if not self.valid or not metrics:
            self.fitness = 1e6 + len(str(self.validation))
        else:
            self.fitness = (
                    metrics.get("lcom_avg",    0.0) +
                    metrics.get("sgm_max",     0.0) +
                    metrics.get("sgm_sd_sum",  0.0) +
                    metrics.get("coupling_max",0.0)
            )

        save_to_db({
            "timestamp":  datetime.utcnow().isoformat(),
            "story":      self.story_name,
            "gen":        self.gen_id,
            "ind":        self.indiv_id,
            "model":      self.model,
            "temp":       self.temperature,
            "valid":      self.valid,
            "validation": self.validation,
            "fitness":    self.fitness,
            "metrics":    self.metrics,
            "genotype":   self.genotype
        })

def crossover(p1: Individual, p2: Individual, gen_id: int, child_id: int) -> Individual:
    temp = random.choice([p1.temperature, p2.temperature])
    return Individual(
        p1.story_name, p1.stories, temp, gen_id, child_id,
        parent=p1.genotype,
        inspirations=deepcopy(p1.inspirations)
    )

def mutate(ind: Individual):
    if random.random() < MUT_RATE:
        ind.temperature = random.choice(TEMP_OPTIONS)

# ──────────────────────────────────────────────────────────
# 8) Bucle evolutivo por archivo (cada txt es independiente)
# ──────────────────────────────────────────────────────────
def run_evolution(story_name: str, stories: str):
    population = [
        Individual(story_name, stories, random.choice(TEMP_OPTIONS), 0, i)
        for i in range(POP_SIZE)
    ]
    records = []

    for gen in range(1, GENERATIONS+1):
        print(f"\n— Story={story_name} · Generación {gen}/{GENERATIONS} —")
        for ind in population:
            ind.gen_id = gen
            start = time.time()
            ind.evaluate()
            elapsed = time.time() - start
            status = "OK" if ind.valid else "ERR"
            print(f"[{gen},{ind.indiv_id}] model={ind.model} temp={ind.temperature:.2f} "
                  f"fit={ind.fitness:.3f} ({status}), t={elapsed:.1f}s")
            rec = {
                "story":      story_name,
                "gen":        ind.gen_id,
                "ind":        ind.indiv_id,
                "model":      ind.model,
                "temp":       ind.temperature,
                "valid":      ind.valid,
                "validation": ind.validation,
                "fitness":    ind.fitness,
                **ind.metrics
            }
            records.append(rec)

        population.sort(key=lambda x: x.fitness)
        parents       = population[:ELITE]
        top_genotypes = [deepcopy(p.genotype) for p in parents]

        offspring = []
        next_id   = 0
        while len(offspring) < POP_SIZE - ELITE:
            p1, p2 = random.sample(parents, 2)
            child  = crossover(p1, p2, gen, next_id)
            child.inspirations = top_genotypes
            mutate(child)
            offspring.append(child)
            next_id += 1

        population = parents + offspring
        for i, p in enumerate(population[:ELITE]):
            p.indiv_id = i

    best = min(population, key=lambda x: x.fitness)
    print(f"\n>> Mejor en {story_name}: gen={best.gen_id}, ind={best.indiv_id}, "
          f"model={best.model}, fit={best.fitness:.3f}, valid={best.valid}")
    return best, records

# ──────────────────────────────────────────────────────────
# 9) Persistencia de resultados (global CSV + mejores por archivo)
# ──────────────────────────────────────────────────────────
def persist_results(per_file_results: dict[str, tuple]):
    # CSV combinado
    all_recs = []
    for _, (_, records) in per_file_results.items():
        all_recs.extend(records)
    csv_path = EXPERIMENT_DIR / "results.csv"
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(all_recs[0].keys()))
        writer.writeheader()
        writer.writerows(all_recs)
    print(f"✅ Metrics CSV guardado en {csv_path}")

    # Genotipos ganadores por archivo
    for story, (best, _) in per_file_results.items():
        out_path = EXPERIMENT_DIR / f"best_{story}.json"
        with open(out_path, "w", encoding="utf-8") as f:
            json.dump(best.genotype, f, ensure_ascii=False, indent=2)
        print(f"✅ Mejor genotipo para {story} guardado en {out_path}")

# ──────────────────────────────────────────────────────────
# 10) Entry Point: procesar cada rq.txt de forma independiente
# ──────────────────────────────────────────────────────────
def main():
    if not USER_STORIES_DIR.exists():
        print(f"ERROR: no existe {USER_STORIES_DIR}", file=sys.stderr)
        sys.exit(1)

    per_file_results = {}
    for txt in sorted(USER_STORIES_DIR.glob("*.txt")):
        name   = txt.name
        text   = txt.read_text(encoding="utf-8", errors="replace")
        best, records = run_evolution(name, text)
        per_file_results[name] = (best, records)

    if per_file_results:
        persist_results(per_file_results)

if __name__ == "__main__":
    main()
