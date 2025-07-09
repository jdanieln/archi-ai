module ServiceMetrics where

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas
import Std
open List

/-- Una operación: nombre y lista de parámetros. -/
structure Operation where
  name   : String
  params : List String

/-- Un servicio: nombre y lista de operaciones. -/
structure Service where
  name : String
  ops  : List Operation

/-- M(s): número de operaciones. -/
def M (s : Service) : Nat := s.ops.length

/-- F(s): número de parámetros distintos. -/
def F (s : Service) : Nat :=
  let allParams := s.ops.foldl (fun acc op => op.params ++ acc) []
  (allParams.eraseDups).length

/-- MF(s): suma total de ocurrencias de parámetros. -/
def MF (s : Service) : Nat :=
  s.ops.foldl (fun acc o => acc + o.params.length) 0

/-- LCOM(s): 1 − MF/(M·F), o 1 si M=0 ∨ F=0. -/
noncomputable def LCOM (s : Service) : Real :=
  if M s = 0 ∨ F s = 0 then 1
  else 1 - (MF s : Real) / (↑(M s * F s) : Real)

/-- Peso CRUD para granularidad funcional (insensible a mayúsculas/minúsculas). -/
def crudWeight (name : String) : Real :=
  match name.toLower with
  | "create" => 4
  | "update" => 3
  | "delete" => 2
  | _        => 1

/-- FGS(s,o): granularidad funcional de la operación. -/
def FGS (s : Service) (o : Operation) : Real := crudWeight o.name

/-- DGS(s,o): granularidad de datos = |params| / F(s). -/
noncomputable def DGS (s : Service) (o : Operation) : Real :=
  if F s = 0 then 0 else (o.params.length : Real) / (F s : Real)

/-- SGM_op(s,o): granularidad combinada por operación. -/
noncomputable def SGM_op (s : Service) (o : Operation) : Real :=
  (FGS s o + DGS s o) / 2

/-- SGM(s): promedio de SGM_op sobre todas las operaciones. -/
noncomputable def SGM (s : Service) : Real :=
  if M s = 0 then 0 else
    let total : Real := s.ops.foldl (fun acc o => acc + SGM_op s o) 0
    total / (M s : Real)

/-- NOO(s): número de operaciones. -/
def NOO (s : Service) : Nat := M s

/-- sgmSd(s): desviación estándar de SGM_op en el servicio. -/
noncomputable def sgmSd (s : Service) : Real :=
  if s.ops.length ≤ 1 then 0 else
    let xs := s.ops.map (SGM_op s)
    let μ := xs.foldl (·+·) 0 / xs.length.toReal
    let var := xs.foldl (fun acc x => acc + (x - μ)^2) 0 / (xs.length - 1).toReal
    Real.sqrt var

/-- Una llamada RPC entre servicios. -/
structure Call where
  caller : String
  callee : String

/-- Fan-out: destinos distintos a los que llama `svcName`. -/
def couplingOut (svcName : String) (calls : List Call) : Nat :=
  let dests := calls.filter (fun c => c.caller == svcName) |>.map (·.callee)
  dests.eraseDups.length
