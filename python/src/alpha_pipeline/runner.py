#!/usr/bin/env python3
import os
import sys
import json
import csv
import random
import time
import tempfile
import subprocess
import warnings
import re
from pathlib import Path
from copy import deepcopy
from datetime import datetime
from typing import Optional, List

warnings.filterwarnings("ignore", category=FutureWarning)

from dotenv import load_dotenv
import litellm
import google.generativeai as genai
import pandas as pd

# ──────────────────────────────────────────────────────────
# 0) Configuración de Rutas y Entorno
# ──────────────────────────────────────────────────────────
PYTHON_ROOT       = Path(__file__).resolve().parents[2]
ENV_PATH          = PYTHON_ROOT / ".env"
LEAN_PROJECT_DIR  = PYTHON_ROOT / "formal"
USER_STORIES_DIR  = PYTHON_ROOT.parent / "data" / "user-stories-datasets"
EXPERIMENT_DIR    = PYTHON_ROOT / "experiments"

EXECUTION_TIMESTAMP = datetime.now().strftime("%Y%m%d_%H%M%S")
CURRENT_EXECUTION_DIR = EXPERIMENT_DIR / f"exec_{EXECUTION_TIMESTAMP}"
RUNS_DIR          = CURRENT_EXECUTION_DIR / "runs"
CSV_MASTER_PATH   = CURRENT_EXECUTION_DIR / "results.csv"
DB_FILE           = CURRENT_EXECUTION_DIR / "program_db.jsonl"

CURRENT_EXECUTION_DIR.mkdir(parents=True, exist_ok=True)
RUNS_DIR.mkdir(parents=True, exist_ok=True)

if ENV_PATH.is_file():
    load_dotenv(dotenv_path=ENV_PATH)

GEMINI_API_KEY = os.getenv("GEMINI_API_KEY", "")
if GEMINI_API_KEY:
    genai.configure(api_key=GEMINI_API_KEY)

# ──────────────────────────────────────────────────────────
# 2) Parámetros Evolutivos Genuinos (Paper)
# ──────────────────────────────────────────────────────────
POP_SIZE        = 10
GENERATIONS     = 5
ELITE           = 5
MUT_RATE        = 0.2
N_INSPIRATIONS  = 3
TEMP_OPTIONS    = [0.5]
MODELS          = ["gemini-3.1-pro-preview", "gpt-5.1"]

# ──────────────────────────────────────────────────────────
# 3) Prompts
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

2) Genotipo padre (ejemplo válido de generación previa):
{parent}

3) Inspiraciones (otros ejemplos válidos y élite, hasta {n_insp}):
{inspirations}

Definición de microservicio:
- Debe tener una sola responsabilidad (1–5 operaciones como máximo).
- Ser independiente y débilmente acoplado.
- Tener un bounded context claro.

Usa el padre y las inspiraciones para proponer una MEJOR arquitectura.

Salida esperada (SOLO JSON):
{{
  "microservices": [
    {{
      "name": "...",
      "ops": [
        {{ "name": "...", "params": ["..."] }},
        ...
      ]
    }},
    ...
  ],
  "calls": [
    {{ "caller": "...", "callee": "..." }},
    ...
  ]
}}

**NO** agregues texto antes ni después del objeto JSON.
"""

def build_prompt(stories: str, parent: Optional[dict] = None, inspirations: Optional[List[dict]] = None) -> str:
    inspirations = inspirations or []
    insp_str = "\n\n".join(json.dumps(i, ensure_ascii=False) for i in inspirations[:N_INSPIRATIONS])
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
# 4) DB Program Helpers
# ──────────────────────────────────────────────────────────
def save_to_db(record: dict):
    with open(DB_FILE, "a", encoding="utf-8") as f:
        f.write(json.dumps(record, ensure_ascii=False) + "\n")

def load_best_n(n: int) -> list[dict]:
    if not DB_FILE.exists(): return []
    try:
        recs = [json.loads(line) for line in DB_FILE.read_text(encoding="utf-8").splitlines() if line.strip()]
        valid_recs = [r for r in recs if r.get("valid") and r.get("fitness") is not None]
        valid_recs.sort(key=lambda r: float(r["fitness"]))
        return [r["genotype"] for r in valid_recs[:n]]
    except Exception:
        return []

# ──────────────────────────────────────────────────────────
# 5) Generación con LLM
# ──────────────────────────────────────────────────────────
def call_llm(model: str, prompt: str, temp: float) -> tuple[dict, str]:
    try:
        if model.startswith("gemini"):
            gemini_model = genai.GenerativeModel(model)
            response = gemini_model.generate_content(
                prompt,
                generation_config=genai.GenerationConfig(temperature=temp)
            )
            raw_content = response.text
        else:
            response = litellm.completion(
                model=model,
                messages=[{"role": "user", "content": prompt}],
                temperature=temp
            )
            raw_content = response.choices[0].message.content
            
        if "```json" in raw_content:
            raw_content = raw_content.split("```json")[1].split("```")[0]
        elif "```" in raw_content:
            raw_content = raw_content.split("```")[1]
            
        match = re.search(r'\{.*\}', raw_content, re.DOTALL)
        if match: raw_content = match.group(0)
        raw_content = re.sub(r',\s*\}', '}', raw_content)
        raw_content = re.sub(r',\s*\]', ']', raw_content)
            
        return json.loads(raw_content), raw_content
    except json.JSONDecodeError as e:
        return {}, raw_content if 'raw_content' in locals() else ""
    except Exception as e:
        print(f"[WARN] API failure {model}: {e}", file=sys.stderr)
        return {}, ""

# ──────────────────────────────────────────────────────────
# 6) Validación en Lean
# ──────────────────────────────────────────────────────────
def lean_evaluate(genotype: dict) -> tuple[bool, str, dict]:
    with tempfile.NamedTemporaryFile(
            mode="w", suffix=".json", delete=False,
            dir=LEAN_PROJECT_DIR, encoding="utf-8"
    ) as tmp:
        try:
            json.dump(genotype, tmp, ensure_ascii=False)
        except Exception as e:
            return False, f"JSON Error: {e}", {}
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
            return False, res.stdout, {}
            
        return (
            data.get("status") == "OK",
            data.get("message", ""),
            data.get("metrics", {})
        )
    finally:
        if os.path.exists(path):
            os.remove(path)

# ──────────────────────────────────────────────────────────
# 7) GA: Individual, Crossover, Mutación
# ──────────────────────────────────────────────────────────
class Individual:
    def __init__(self, story_name: str, stories: str,
                 temp: float, gen_id: int, ind_id: int, model: str,
                 parent: Optional[dict]=None, inspirations: Optional[List[dict]]=None):
        self.story_name    = story_name
        self.stories       = stories
        self.temperature   = temp
        self.gen_id        = gen_id
        self.indiv_id      = ind_id
        self.model         = model
        self.parent        = parent
        self.inspirations  = inspirations or []
        self.genotype      = None
        self.valid         = False
        self.validation    = ""
        self.metrics       = {}
        self.fitness       = float("inf")

    def evaluate(self):
        # Si el individuo ya tiene un genotipo válido (ej. copiado de élite), no re-evaluar
        if getattr(self, "genotype", None) is not None and getattr(self, "valid", False):
            # Simulamos que costó 0 tiempo de API y usamos las métricas cacheadas
            self.metrics["time_llm"] = 0.0
            self.metrics["time_lean"] = 0.0
            
            # Guardamos el snapshot de historia para esta generación
            save_to_db({
                "timestamp":  datetime.now().isoformat(),
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
            return

        global_insp = load_best_n(N_INSPIRATIONS)
        insp = (self.inspirations or []) + global_insp
        
        prompt = build_prompt(self.stories, self.parent, insp)
        
        start_llm = time.time()
        self.genotype, raw = call_llm(self.model, prompt, self.temperature)
        self.metrics["time_llm"] = round(time.time() - start_llm, 2)
        
        if not self.genotype:
            self.valid = False
            self.validation = "Invalid JSON / Generation Error"
            self.metrics["time_lean"] = 0
        else:
            start_lean = time.time()
            self.valid, self.validation, metrics = lean_evaluate(self.genotype)
            self.metrics["time_lean"] = round(time.time() - start_lean, 2)
            self.metrics.update(metrics)

        if not self.valid or not self.metrics.get("lcom_avg") is not None:
            self.fitness = 1e6 + len(str(self.validation))
        else:
            self.fitness = (
                    self.metrics.get("lcom_avg",    0.0) +
                    self.metrics.get("sgm_max",     0.0) +
                    self.metrics.get("sgm_sd_sum",  0.0) +
                    self.metrics.get("coupling_max",0.0)
            )

        save_to_db({
            "timestamp":  datetime.now().isoformat(),
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
    # Mantener el modelo del padre base
    return Individual(
        p1.story_name, p1.stories, temp, gen_id, child_id, p1.model,
        parent=p1.genotype,
        inspirations=deepcopy(p1.inspirations)
    )

def mutate(ind: Individual):
    if random.random() < MUT_RATE:
        ind.temperature = random.choice(TEMP_OPTIONS)

# ──────────────────────────────────────────────────────────
# 8) Bucle de Evolución
# ──────────────────────────────────────────────────────────
def run_evolution(story_name: str, stories: str, model: str):
    population = [
        Individual(story_name, stories, random.choice(TEMP_OPTIONS), 1, i, model)
        for i in range(POP_SIZE)
    ]
    records = []

    for gen in range(1, GENERATIONS + 1):
        print(f"\n— Model={model} · Story={story_name} · Generación {gen}/{GENERATIONS} —")
        
        # Evaluación de la población
        for ind in population:
            ind.gen_id = gen
            start = time.time()
            ind.evaluate()
            elapsed = time.time() - start
            status = "OK" if ind.valid else "ERR"
            print(f"[{gen},{ind.indiv_id}] temp={ind.temperature:.2f} "
                  f"fit={ind.fitness:.3f} ({status}), t={elapsed:.1f}s")
                  
            rec = {
                "story":      story_name,
                "gen":        ind.gen_id,
                "ind":        ind.indiv_id,
                "model":      ind.model,
                "temp":       ind.temperature,
                "valid":      ind.valid,
                "validation": ind.validation,
                "fitness":    ind.fitness if ind.valid else None,
                "time_llm":   ind.metrics.get("time_llm", 0),
                "time_lean":  ind.metrics.get("time_lean", 0),
                "sgm_sd_sum": ind.metrics.get("sgm_sd_sum", None),
                "sgm_max":    ind.metrics.get("sgm_max", None),
                "lcom_avg":   ind.metrics.get("lcom_avg", None),
                "coupling_max":ind.metrics.get("coupling_max", None)
            }
            records.append(rec)

        # Selección natural (Elitismo)
        population.sort(key=lambda x: x.fitness)
        parents       = population[:ELITE]
        top_genotypes = [deepcopy(p.genotype) for p in parents if p.genotype]

        # Cruce y Reemplazo
        if gen < GENERATIONS:
            offspring = []
            next_id   = ELITE
            while len(offspring) < POP_SIZE - ELITE:
                p1, p2 = random.sample(parents, 2)
                child  = crossover(p1, p2, gen + 1, next_id)
                child.inspirations = top_genotypes
                mutate(child)
                offspring.append(child)
                next_id += 1

            population = parents + offspring
            for i, p in enumerate(population[:ELITE]):
                p.indiv_id = i

    best = min(population, key=lambda x: x.fitness)
    status_best = "OK" if best.valid else "FAIL"
    print(f"\n>> Mejor {model} en {story_name}: gen={best.gen_id}, ind={best.indiv_id}, fit={best.fitness:.3f} ({status_best})")
    return best, records

# ──────────────────────────────────────────────────────────
# 9) Main
# ──────────────────────────────────────────────────────────
def main():
    if not USER_STORIES_DIR.exists():
        print(f"ERROR: {USER_STORIES_DIR} no encontrado.")
        sys.exit(1)

    all_results = []
    datasets = sorted(USER_STORIES_DIR.glob("*.txt"))
    
    total_executions = len(MODELS) * len(datasets) * POP_SIZE * GENERATIONS
    print(f"🚀 Iniciando Pipeline Evolutivo Real (GA). Evaluaciones Maximas: {total_executions}")
    
    for txt in datasets:
        dataset_id = txt.stem
        stories = txt.read_text(encoding="utf-8", errors="replace")
        
        for model in MODELS:
            best, records = run_evolution(dataset_id, stories, model)
            all_results.extend(records)
            
            # Guardamos el archivo json de corrida por LLM
            out_path = RUNS_DIR / f"best_{model.replace('/', '_')}_{dataset_id}.json"
            with open(out_path, "w", encoding="utf-8") as f:
                json.dump(best.genotype if best.genotype else {}, f, ensure_ascii=False, indent=2)

    # Persistir CSV final global
    if all_results:
        df = pd.DataFrame(all_results)
        df.to_csv(CSV_MASTER_PATH, index=False)
        print(f"📊 Exportado CSV global a: {CSV_MASTER_PATH}")

if __name__ == "__main__":
    main()
