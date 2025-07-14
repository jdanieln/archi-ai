import Lean.Data.Json
import ServiceMetrics

open Lean Json ServiceMetrics

deriving instance FromJson for Operation
deriving instance FromJson for Service
deriving instance FromJson for Call

structure Genotype where
  services : List Service
  calls    : List Call
  deriving FromJson, Repr

/--
  Valida el `Genotype`. Ahora esta función es 100% computable.
-/
def validateGenotype (gt : Genotype) : Except String Unit := do
  let serviceNames := gt.services.map (·.name)

  for c in gt.calls do
    if c.caller == c.callee then throw s!"Self-call: {c.caller}"
    unless serviceNames.contains c.caller do throw s!"Unknown caller: {c.caller}"
    unless serviceNames.contains c.callee do throw s!"Unknown callee: {c.callee}"

  let maxCoupling := if gt.services.isEmpty then 0 else gt.services.length - 1
  for svc in gt.services do
    -- Ahora comparamos con Floats. Añadimos `.0` para claridad.
    if LCOM svc > 0.8 then
      throw s!"{svc.name}: Low cohesion (LCOM > 0.8)"
    if couplingOut svc.name gt.calls > maxCoupling then
      throw s!"{svc.name}: High coupling (Coupling > {maxCoupling})"
    if SGM svc > 2.5 then
      throw s!"{svc.name}: High granularity (SGM > 2.5)"
    if sgmSd svc > 0.5 then
      throw s!"{svc.name}: Inconsistent granularity (SGM SD > 0.5)"
  pure ()

/--
  Punto de entrada. Como todo es computable, la estructura es muy simple.
-/
def main (args : List String) : IO UInt32 := do
  if args.length != 1 then
    -- Recuerda que el nombre del ejecutable lo definimos en el lakefile
    IO.eprintln "Uso: lake exe validate <ruta_al_genotipo.json>"
    return 1

  let filePath := args.head!
  try
    let content ← IO.FS.readFile filePath
    -- Todo se puede encadenar en un solo bloque `do` porque todo es computable.
    let result := do
      let json ← Json.parse content
      let genotype ← fromJson? (α := Genotype) json
      validateGenotype genotype

    match result with
    | .error err => IO.eprintln s!"Error: {err}"; return 1
    | .ok _      => IO.println "OK"; return 0
  catch e =>
    IO.eprintln s!"Error de I/O: {e}"
    return 1
