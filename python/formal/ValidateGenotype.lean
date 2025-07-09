import Std
import Lean.Data.Json
import ServiceMetrics  -- Import con prefijo del paquete

/-!
  ValidateGenotype.lean
  Valida un genotipo de arquitectura de servicios
!-/

open Lean
open Lean.Json
open Std
open formal.ServiceMetrics  -- Abrir el namespace para acceder a las definiciones

/-- Decodifica un JSON en una `Operation`. -/
def decodeOperation (j : Json) : Except String Operation := do
  unless j.isObj do throw "Expected object for operation"
  let name      ← j.getObjValAs? String "name" <|> throw "Missing 'name' in operation"
  let rawParams ← j.getObjValAs? (Array Json) "params" <|> pure #[]
  let params    ← rawParams.toList.mapM (fun j =>
                    match j.getStr? with
                    | some p => pure p
                    | none   => throw s!"Non-string parameter in operation {name}")
  return { name := name, params := params }

/-- Decodifica un JSON en un `Service`. -/
def decodeService (j : Json) : Except String Service := do
  unless j.isObj do throw "Expected object for service"
  let name   ← j.getObjValAs? String "name" <|> throw "Missing 'name' in service"
  let rawOps ← j.getObjValAs? (Array Json) "operations" <|> pure #[]
  let ops    ← rawOps.toList.mapM decodeOperation
  return { name := name, ops := ops }

/-- Decodifica un JSON en una `Call`. -/
def decodeCall (j : Json) : Except String Call := do
  unless j.isObj do throw "Expected object for call"
  let caller ← j.getObjValAs? String "caller" <|> throw "Missing 'caller' in call"
  let callee ← j.getObjValAs? String "callee" <|> throw "Missing 'callee' in call"
  return { caller := caller, callee := callee }

/-- Representa el genotipo completo: servicios y llamadas. -/
structure Genotype where
  services : List Service
  calls    : List Call

/-- Parsea todo el `String` JSON a `Genotype`. -/
def parseGenotype (s : String) : Except String Genotype := do
  let j      ← Json.parse s
  let rawSv  ← j.getObjValAs? (Array Json) "services" <|> throw "Missing 'services' array"
  let rawCs  ← j.getObjValAs? (Array Json) "calls" <|> pure #[]
  let svs    ← rawSv.toList.mapM decodeService
  let cs     ← rawCs.toList.mapM decodeCall
  return { services := svs, calls := cs }

/-- Valida las invariantes del genotipo con mensajes de error mejorados -/
noncomputable def validateGenotype (gt : Genotype) : Except String Unit := do
  let nameSet := HashSet.empty.insertList (gt.services.map (·.name))

  -- Validar llamadas
  for c in gt.calls do
    if c.caller == c.callee then
      throw s!"Self-call not allowed: service '{c.caller}' calls itself"
    if !nameSet.contains c.caller then
      throw s!"Caller service not declared: '{c.caller}'"
    if !nameSet.contains c.callee then
      throw s!"Callee service not declared: '{c.callee}'"

  -- Validar métricas por servicio
  for svc in gt.services do
    let lcomVal := LCOM svc
    if lcomVal > 0.8 then
      throw s!"Service '{svc.name}' has low cohesion (LCOM = {lcomVal:.3f} > 0.8)"

    let fanOut := couplingOut svc.name gt.calls
    let maxFanOut := gt.services.length - 1
    if fanOut > maxFanOut then
      throw s!"Service '{svc.name}' has excessive coupling (fan-out = {fanOut} > {maxFanOut})"

    let sgmVal := SGM svc
    if sgmVal > 2.5 then
      throw s!"Service '{svc.name}' has excessive granularity (SGM = {sgmVal:.3f} > 2.5)"

    let sdVal := sgmSd svc
    if sdVal > 0.5 then
      throw s!"Service '{svc.name}' has inconsistent granularity (SD = {sdVal:.3f} > 0.5)"

  pure ()

/-- Punto de entrada mejorado con manejo de errores detallado -/
noncomputable def main (args : List String) : IO UInt32 := do
  match args with
  | [filePath] =>
    try
      let content ← IO.FS.readFile filePath
      match parseGenotype content with
      | Except.error e => IO.eprintln s!"JSON parse error: {e}"; return 1
      | Except.ok gt   =>
        match validateGenotype gt with
        | Except.error e => IO.eprintln s!"Validation failed: {e}"; return 1
        | Except.ok _    => IO.println "✓ Genotype validated successfully"; return 0
    catch e =>
      IO.eprintln s!"File error: {e}"; return 1
  | _ =>
    IO.eprintln "Usage: validate_genotype <path_to_genotype.json>"
    IO.eprintln "Example: validate_genotype genotype.json"
    return 1
