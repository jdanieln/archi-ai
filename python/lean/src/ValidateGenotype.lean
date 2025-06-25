import ServiceMetrics
import Std.Data.Json

open Lean.Json
open ServiceMetrics

/-- LECTURA DE ARGUMENTOS, JSON Y DECODIFICACIÓN --/
def readJson (path : String) : IO (Except String Json) := do
  let txt ← IO.FS.readFile path
  match Json.parse txt with
  | Except.ok j  => pure (Except.ok j)
  | Except.error e => pure (Except.error s!"JSON parse error: {e}")

def decodeJson {α : Type} [FromJson α] (j : Json) : Except String α :=
  match fromJson? j with
  | Except.ok x  => Except.ok x
  | Except.error e => Except.error s!"JSON decode error: {e}"

/-- ESTRUCTURAS LOCALES REFLEJANDO TU GENOTIPO JSON --/
structure Call where
  from : String
  to   : String

instance : FromJson Call where
  fromJson? j := do
    let o ← j.asObj?
    let fm ← o.get? "from" |>.andThen Json.getStr?
    let to ← o.get? "to"   |>.andThen Json.getStr?
    pure ⟨fm, to⟩

structure Operation where
  name   : String
  params : List String

instance : FromJson Operation where
  fromJson? j := do
    let o    ← j.asObj?
    let nm   ← o.get? "name"   |>.andThen Json.getStr?
    let arr  ← o.get? "params" |>.andThen Json.getArr?
    let ps   ← arr.mapM Json.getStr?
    pure ⟨nm, ps⟩

structure Service where
  name       : String
  operations : List Operation

instance : FromJson Service where
  fromJson? j := do
    let o   ← j.asObj?
    let nm  ← o.get? "name"       |>.andThen Json.getStr?
    let arr ← o.get? "operations" |>.andThen Json.getArr?
    let ops ← arr.mapM fromJson?
    pure ⟨nm, ops⟩

structure Genotype where
  services : List Service
  calls    : List Call

instance : FromJson Genotype where
  fromJson? j := do
    let o   ← j.asObj?
    let svs ← o.get? "services" |>.andThen Json.getArr? |>.andThen fun arr => arr.mapM fromJson?
    let cs  ← o.get? "calls"    |>.andThen Json.getArr? |>.andThen fun arr => arr.mapM fromJson?
    pure ⟨svs, cs⟩

/-- PROGRAMA PRINCIPAL: LEE, DECODIFICA Y CHEQUEA INVARIANTES --/
def main : IO UInt32 := do
  let args ← IO.getArgs
  if args.size ≠ 1 then
    IO.eprintln "Uso: verifyGenotype <ruta-json>"
    return 1

  match ← readJson args[0] with
  | Except.error e =>
    IO.eprintln e; return 1
  | Except.ok j =>
    match decodeJson (j : Json) with
    | Except.error e =>
      IO.eprintln e; return 1
    | Except.ok gt =>
      -- 1) cohesion mínima
      for svc in gt.services do
        if LCOM svc > 0.8 then
          IO.eprintln s!"❌ {svc.name}: LCOM = {LCOM svc} > 0.8"
          return 1
      -- 2) variabilidad de granularidad
      for svc in gt.services do
        if sgmSd svc > 0.5 then
          IO.eprintln s!"❌ {svc.name}: SGM-σ = {sgmSd svc} > 0.5"
          return 1
      -- 3) acoplamiento máximo
      for svc in gt.services do
        let co := couplingOut svc.name gt.calls
        if co > 10 then
          IO.eprintln s!"❌ {svc.name}: CouplingOut = {co} > 10"
          return 1
      -- si llegó hasta aquí, todo OK
      IO.println "OK"
      return 0
