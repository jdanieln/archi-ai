import Lean
import Lean.Data.Json
import ServiceMetrics -- Importa tu archivo local con métricas

open Lean Json ServiceMetrics

-- Si Operation, Service y Call están definidos en ServiceMetrics, no los repitas aquí.
deriving instance FromJson for Operation
deriving instance FromJson for Service
deriving instance FromJson for Call

structure Genotype where
  services : List Service
  calls    : List Call
  deriving FromJson, Repr

/-- Valida el `Genotype`. Es `noncomputable` porque usa LCOM y sgmSd. -/
noncomputable def validateGenotype (gt : Genotype) : Except String Unit := do
  let serviceNames := gt.services.map (·.name)

  for c in gt.calls do
    if c.caller == c.callee then throw s!"Self-call: {c.caller}"
    unless serviceNames.contains c.caller do throw s!"Unknown caller: {c.caller}"
    unless serviceNames.contains c.callee do throw s!"Unknown callee: {c.callee}"

  let maxCoupling := if gt.services.isEmpty then 0 else gt.services.length - 1
  for svc in gt.services do
    if LCOM svc > 0.8 then
      throw s!"{svc.name}: Low cohesion (LCOM > 0.8)"
    if couplingOut svc.name gt.calls > maxCoupling then
      throw s!"{svc.name}: High coupling (Coupling > {maxCoupling})"
    if SGM svc > 2.5 then
      throw s!"{svc.name}: High granularity (SGM > 2.5)"
    if sgmSd svc > 0.5 then
      throw s!"{svc.name}: Inconsistent granularity (SGM SD > 0.5)"
  pure ()

/-- Punto de entrada del programa. Es `noncomputable` y maneja toda la I/O. -/
noncomputable def main : IO UInt32 := do
  -- Usa una ruta fija para el JSON (por ejemplo, formal/genotype.json)
  let filePath := "genotype.json"
  try
    let content ← IO.FS.readFile filePath

    let result := do
      let json ← Json.parse content
      let genotype ← fromJson? (α := Genotype) json
      validateGenotype genotype

    match result with
    | .error err => IO.eprintln s!"Error: {err}"; return (1 : UInt32)
    | .ok _      => IO.println "OK"; return (0 : UInt32)

  catch e =>
    IO.eprintln s!"Error inesperado: {e}"
    return (1 : UInt32)
