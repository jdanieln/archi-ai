-- file: FormalMetricsProject/ValidateGenotype.lean

/-
Verificador de “Genotype” JSON:
  • Usa Lean.Data.Json para parsear
  • Importa tu ServiceMetrics
-/
import Lean.Data.Json.Basic -- Importación correcta para JSON
import ServiceMetrics      -- Tu módulo de métricas

open Lean.Json            -- Para Json.parse?, Json.getObjVal?, Json.getStr?, Json.getArr?, Json.as?
open ServiceMetrics       -- Para tus estructuras y funciones de ServiceMetrics

-- No necesitamos JOperation, JService, JCall, JGenotype si decodificamos directamente a las de ServiceMetrics.

/--
  Parsea una Json que representa una operación a ServiceMetrics.Operation.
  Espera { "name": string, "params": [string,...] }
-/
partial def decodeOperation (j : Json) : Except String Operation := do
  let nameJson   ← j.getObjVal? "name"
  let name       ← nameJson.as? String
  let paramsJson ← j.getObjVal? "params"
  let paramsArr  ← paramsJson.getArr?
  let params     ← paramsArr.toList.mapM (fun p => p.as? String)
  pure { name := name, params := params }

/--
  Parsea una Json que representa un servicio a ServiceMetrics.Service.
  Espera { "name": string, "operations": [ {...}, ... ] }
-/
partial def decodeService (j : Json) : Except String Service := do
  let nameJson   ← j.getObjVal? "name"
  let name       ← nameJson.as? String
  let opsJson    ← j.getObjVal? "operations"
  let opsArr     ← opsJson.getArr?
  let opsList    ← opsArr.toList.mapM decodeOperation
  pure { name := name, ops := opsList }

/--
  Parsea una Json que representa una llamada RPC a ServiceMetrics.Call.
  Espera { "caller": string, "callee": string }
  (Ajustado para coincidir con ServiceMetrics.Call)
-/
partial def decodeCall (j : Json) : Except String Call := do
  let callerJson ← j.getObjVal? "caller"
  let caller     ← callerJson.as? String
  let calleeJson ← j.getObjVal? "callee"
  let callee     ← calleeJson.as? String
  pure { caller := caller, callee := callee }

/-- Estructura completa del genotipo (usando ServiceMetrics.Service y ServiceMetrics.Call) --/
structure Genotype where
  services : List Service
  calls    : List Call

/--
  Parsea el JSON completo a `Genotype`.
  Debe tener las claves "services" y "calls" en la raíz.
-/
partial def parseGenotype (content : String) : Except String Genotype := do
  -- 1) De String → Json
  let j ← match Json.parse? content with -- Usar Json.parse?
    | Except.error err => throw s!"JSON inválido: {err}"
    | Except.ok js     => pure js

  -- 2) Extraer el arreglo de servicios
  let sArrJson   ← j.getObjVal? "services"
  let sArr       ← sArrJson.getArr?
  let services   ← sArr.toList.mapM decodeService

  -- 3) Extraer el arreglo de llamadas
  let cArrJson   ← j.getObjVal? "calls"
  let cArr       ← cArrJson.getArr?
  let calls      ← cArr.toList.mapM decodeCall

  pure { services := services, calls := calls }

/--
  Valida tu `Genotype` aplicando invariantes basadas en ServiceMetrics.
-/
def validateGenotype (gt : Genotype) : Except String Unit := do
  -- 1) No self-calls
  for c in gt.calls do
    if c.caller = c.callee then throw s!"Self-call detectada: {c.caller}"

  -- 2) Sólo llamadas entre servicios declarados
  let names := gt.services.map (·.name)
  for c in gt.calls do
    if !names.contains c.caller then throw s!"Llamada desde servicio no declarado: {c.caller}"
    if !names.contains c.callee   then throw s!"Llamada hacia servicio no declarado: {c.callee}"

  -- 3) Cohesión mínima (LCOM > 0.8)
  for svc in gt.services do
    let l := ServiceMetrics.LCOM svc
    if l > 0.8 then -- LCOM debe estar entre 0 y 1, si es > 0.8 es baja cohesión
      throw s!"'{svc.name}': LCOM = {l} > 0.8 (baja cohesión)"

  -- 4) Acoplamiento máximo (fan-out ≤ servicios−1)
  let maxTargets := (gt.services.length - 1).toNat -- .toNat previene Nat negativos si length es 0
  for svc in gt.services do
    let co := ServiceMetrics.couplingOut svc.name gt.calls
    if co > maxTargets then
      throw s!"'{svc.name}': CouplingOut = {co} > {maxTargets} (acoplamiento excesivo)"

  -- 5) Granularidad media (SGM > 2.5)
  for svc in gt.services do
    let g := ServiceMetrics.SGM svc
    if g > 2.5 then
      throw s!"'{svc.name}': SGM = {g} > 2.5 (granularidad excesiva)"

  -- 6) Desviación estándar de granularidad (sgmSd > 0.5 - ejemplo de invariante)
  for svc in gt.services do
    let sd := ServiceMetrics.sgmSd svc
    if sd > 0.5 then -- Ejemplo: si la desviación estándar es muy alta, las operaciones son muy dispares
      throw s!"'{svc.name}': sgmSd = {sd} > 0.5 (granularidad inconsistente)"

  pure ()

/--
  Función principal: lee el fichero pasado como primer argumento,
  parsea y valida. Imprime “OK” o el error correspondiente.
-/
@[entryPoint]
def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "Uso: verifyGenotype <genotype.json>"
    return 1

  let path := args[0]!
  let content ← IO.FS.readFile path

  match parseGenotype content with
  | Except.error perr =>
    IO.eprintln s!"[Lean] Error parseando JSON: {perr}"
    return 1
  | Except.ok gt      =>
    match validateGenotype gt with
    | Except.error verr =>
      IO.eprintln s!"[Lean] Error de validación: {verr}"
      return 1
    | Except.ok _       =>
      IO.println "OK"
      return 0
