-- Formal/ValidateGenotype.lean

import Std                   -- IO, IO.FS, List.mapM
import Lean.Data.Json        -- Json.parse, getObjValAs?, Json.getStr?
import ServiceMetrics        -- carga Operation, Service, Call, LCOM, SGM, couplingOut…

/-!
  ValidateGenotype.lean

  Parsea un JSON de genotipo (servicios + llamadas) y valida 6 invariantes:
    1. No self-calls
    2. Sólo llamadas entre servicios declarados
    3. Cohesión mínima: LCOM ≤ 0.8
    4. Acoplamiento máximo: fan-out ≤ nServices − 1
    5. Granularidad máxima: SGM ≤ 2.5
    6. Desviación estándar de granularidad ≤ 0.5
!-/

open Lean
open Lean.Json
open Std
open ServiceMetrics

/-- Decodifica un JSON en una `Operation`. -/
def decodeOperation (j : Json) : Except String Operation := do
  let name      ← j.getObjValAs? String      "name"
  let rawParams ← j.getObjValAs? (Array Json) "params"
  let params    ← rawParams.toList.mapM Json.getStr?
  return { name := name, params := params }

/-- Decodifica un JSON en un `Service`. -/
def decodeService (j : Json) : Except String Service := do
  let name   ← j.getObjValAs? String         "name"
  let rawOps ← j.getObjValAs? (Array Json)   "operations"
  let ops    ← rawOps.toList.mapM decodeOperation
  return { name := name, ops := ops }

/-- Decodifica un JSON en una `Call`. -/
def decodeCall (j : Json) : Except String Call := do
  let caller ← j.getObjValAs? String "caller"
  let callee ← j.getObjValAs? String "callee"
  return { caller := caller, callee := callee }

/-- Representa el genotipo completo: servicios y llamadas. -/
structure Genotype where
  services : List Service
  calls    : List Call

/-- Parsea todo el `String` JSON a `Genotype`. -/
def parseGenotype (s : String) : Except String Genotype := do
  let j      ← Json.parse s
  let rawSv  ← j.getObjValAs? (Array Json) "services"
  let rawCs  ← j.getObjValAs? (Array Json) "calls"
  let svs    ← rawSv.toList.mapM decodeService
  let cs     ← rawCs.toList.mapM decodeCall
  return { services := svs, calls := cs }

/-- Valida las seis invariantes del genotipo. -/
noncomputable def validateGenotype (gt : Genotype) : Except String Unit := do
  let names := gt.services.map (·.name)

  for c in gt.calls do
    if c.caller == c.callee then
      throw s!"Self-call detected: {c.caller}"
    if !names.contains c.caller then
      throw s!"Call from undeclared service: {c.caller}"
    if !names.contains c.callee then
      throw s!"Call to undeclared service: {c.callee}"

  for svc in gt.services do
    if LCOM svc > 0.8 then
      throw s!"'{svc.name}': Low cohesion (LCOM > 0.8)"
    if couplingOut svc.name gt.calls > gt.services.length - 1 then
      throw s!"'{svc.name}': Excessive coupling (fan-out > {gt.services.length - 1})"
    if SGM svc > 2.5 then
      throw s!"'{svc.name}': Excessive granularity (SGM > 2.5)"
    if sgmSd svc > 0.5 then
      throw s!"'{svc.name}': Inconsistent granularity (sgmSd > 0.5)"

  pure ()

/-- Punto de entrada; devuelve 0 en OK, 1 en error. -/
noncomputable def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "Usage: validate_genotype <path_to_genotype.json>"
    return 1
  let content ← IO.FS.readFile args.head!
  match parseGenotype content with
  | Except.error e => IO.eprintln s!"JSON parse error: {e}"; return 1
  | Except.ok gt   =>
    match validateGenotype gt with
    | Except.error e => IO.eprintln s!"Validation error: {e}"; return 1
    | Except.ok _    => IO.println "OK"; return 0
