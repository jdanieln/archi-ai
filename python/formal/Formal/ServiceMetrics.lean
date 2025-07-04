/-
lean/src/ServiceMetrics.lean

Define operaciones y servicios, métricas LCOM, SGM, NOO, couplingOut y
sgmSd (desviación estándar de SGM_op), usando exclusivamente mathlib4.
-/
import Mathlib.Data.Real.Basic      -- Real, ℝ, sqrt
import Mathlib.Data.List.Basic      -- List.bind, List.foldl, List.map, List.filter
import Mathlib.Data.List.Lemmas      -- eraseDups

namespace ServiceMetrics

def Param := String

structure Operation where
  name   : String
  params : List Param

structure Service where
  name : String
  ops  : List Operation

/-- M(s): número de operaciones. -/
def M (s : Service) : Nat := s.ops.length

/-- F(s): número de parámetros distintos. -/
def F (s : Service) : Nat := (s.ops.bind (·.params)).eraseDups.length

/-- MF(s): suma total de parámetros. -/
def MF (s : Service) : Nat := s.ops.foldl (fun acc o => acc + o.params.length) 0

/-- LCOM normalizado. -/
def LCOM (s : Service) : Real :=
  if s.M = 0 ∨ s.F = 0 then 1 else
    1 - (MF s : Real) / Real.ofNat (s.M * s.F)

/-- Peso CRUD. -/
def crudWeight : String → Real
  | "create" := 4
  | "update" := 3
  | "delete" := 2
  | _        := 1

/-- FGS: granularidad funcional de una operación. -/
def FGS (s : Service) (o : Operation) : Real := crudWeight o.name

/-- DGS: granularidad de datos (|params|/F). -/
def DGS (s : Service) (o : Operation) : Real :=
  if s.F = 0 then 0 else (o.params.length : Real) / Real.ofNat (s.F)

/-- SGM_op: granularidad combinada. -/
def SGM_op (s : Service) (o : Operation) : Real := (FGS s o + DGS s o) / 2

/-- SGM: promedio de SGM_op. -/
def SGM (s : Service) : Real :=
  if s.M = 0 then 0 else (s.ops.foldl (fun acc o => acc + SGM_op s o) 0) / Real.ofNat (s.M)

/-- NOO: número de operaciones. -/
def NOO (s : Service) : Nat := s.M

end ServiceMetrics

open ServiceMetrics

/-- Una llamada RPC. -/
structure Call where
  from : String
  to   : String

/-- CouplingOut: destinos distintos a los que llama svcName. -/
def couplingOut (svcName : String) (calls : List Call) : Nat :=
  (calls.filter (·.from = svcName)).map (·.to).eraseDups.length

/-- sgmSd: desviación estándar de SGM_op. -/
def sgmSd (s : Service) : Real :=
  if s.ops.isEmpty then 0 else
    let xs  := s.ops.map (SGM_op s)
    let μ   := xs.foldl (· + ·) 0 / Real.ofNat s.ops.length
    let var := xs.foldl (fun acc x => acc + (x - μ) ^ 2) 0 / Real.ofNat s.ops.length
    Real.sqrt var
