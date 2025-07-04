-- file: lean/ValidateGenotype/src/ValidateGenotype.lean

import Std.Data.Json
import ServiceMetrics

open Lean.Json
open ServiceMetrics

/-- Decodificar un ServiceMetrics.Operation desde JSON --/
partial def decodeOperation (j : Json) : Except String Operation := do
  let obj    ← j.getObj?      | Except.error "Operation no es un objeto"
  let nm     ← obj.getStrVal? "name"
  let arr    ← obj.getArrVal? "params"
  let ps     ← arr.toList.mapM fun p => p.getStr? |>.mapError (fun _ => "Parámetro no es string")
  pure { name := nm, params := ps }

/-- Decodificar un ServiceMetrics.Service (sin el campo name) --/
partial def decodeService (j : Json) : Except String Service := do
  let obj ← j.getObj?                | Except.error "Service no es un objeto"
  let nm  ← obj.getStrVal? "name"
  let arr ← obj.getArrVal? "operations"
  let ops ← arr.toList.mapM decodeOperation
  pure { name := nm, ops := ops }

/-- Decodificar un ServiceMetrics.Call desde JSON --/
partial def decodeCall (j : Json) : Except String Call := do
  let obj ← j.getObj?    | Except.error "Call no es un objeto"
  let fr  ← obj.getStrVal? "from"
  let to_ ← obj.getStrVal? "to"
  pure { from := fr, to := to_ }

/-- Estructura completa del genotipo --/
structure Genotype where
  services : List Service
  calls    : List Call

/-- Decodificar todo el Genotype --/
partial def decodeGenotype (j : Json) : Except String Genotype := do
  let servicesJ ← j.getArrVal? "services"
  let services  ← servicesJ.toList.mapM decodeService
  let callsJ    ← j.getArrVal? "calls"
  let calls     ← callsJ.toList.mapM decodeCall
  pure { services := services, calls := calls }

/-- Chequea todas tus invariantes --/
def validateGenotype (gt : Genotype) : Except String Unit := do
  -- 1) No self-calls
  for c in gt.calls do
    if c.from = c.to then throw s!"Self-call detectada: {c.from}"

  -- 2) Sólo llamadas entre servicios declarados
  let names := gt.services.map (·.name)
  for c in gt.calls do
    if !names.contains c.from then throw s!"Llamada desde no declarado: {c.from}"
    if !names.contains c.to   then throw s!"Llamada hacia no declarado: {c.to}"

  -- 3) Cohesión mínima
  for svc in gt.services do
    if LCOM svc > 0.8 then
      throw s!"'{svc.name}': LCOM = {LCOM svc} > 0.8"

  -- 4) Acoplamiento máximo (fan-out ≤ servicios−1)
  let maxTargets := gt.services.length - 1
  for svc in gt.services do
    let co := coupling svc.name gt.calls
    if co > maxTargets then
      throw s!"'{svc.name}': CouplingOut = {co} > {maxTargets}"

  -- 5) Granularidad media
  for svc in gt.services do
    let g := SGM svc
    if g > 2.5 then
      throw s!"'{svc.name}': SGM = {g} > 2.5"

  pure ()

/-- Entry point del ejecutable --/
@[entryPoint]
def main (args : List String) : IO UInt32 := do
  match args with
  | [filePath] =>
    match Json.parse? (← IO.FS.readFile filePath) with
    | Except.error err =>
      IO.eprintln s!"[Lean] JSON inválido: {err}"; return 1
    | Except.ok j =>
      match decodeGenotype j with
      | Except.error err =>
        IO.eprintln s!"[Lean] Error decodificando: {err}"; return 1
      | Except.ok gt =>
        match validateGenotype gt with
        | Except.error msg =>
          IO.eprintln s!"[Lean] Falló invariante: {msg}"; return 1
        | Except.ok _ =>
          IO.println "OK"; return 0
  | _ =>
    IO.eprintln "Uso: verifyGenotype <genotype.json>"
    return 1
