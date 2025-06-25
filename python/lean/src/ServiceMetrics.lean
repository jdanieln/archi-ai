import Std.Data.List.Basic
import Std.Data.List.Lemmas
import Mathlib.Data.Real.Basic  -- Real, ℝ

/-
  Definiciones de estructura
-/
def Param := String

structure Operation where
  name   : String
  params : List Param

structure Service where
  ops : List Operation

/-
  Métricas intrínsecas al servicio
-/
namespace ServiceMetrics

/-- Número de operaciones -/
def M (s : Service) : Nat := s.ops.length

/-- Número de parámetros únicos -/
def F (s : Service) : Nat :=
  (s.ops.bind (·.params)).eraseDup.length

/-- Suma de todas las ocurrencias de parámetros -/
def MF (s : Service) : Nat :=
  s.ops.sum (·.params.length)

/-- LCOM normalizado: 1 − MF/(M·F) o 1 si M=0 ∨ F=0 -/
def LCOM (s : Service) : Real :=
  if s.M = 0 ∨ s.F = 0 then 1
  else 1 - (MF s : Real) / (Real.ofNat (s.M * s.F))

/-- Peso CRUD para granularidad funcional -/
def crudWeight : String → Real
  | "create" := 4
  | "update" := 3
  | "delete" := 2
  | _        := 1

/-- FGS: granularidad funcional de una operación -/
def FGS (s : Service) (o : Operation) : Real :=
  crudWeight o.name

/-- DGS: granularidad de datos (parámetros) de una operación, normalizada en [0,1] -/
def DGS (s : Service) (o : Operation) : Real :=
  if s.F = 0 then 0 else (o.params.length : Real) / (Real.ofNat (s.F))

/-- SGM_op: granularidad combinada por operación -/
def SGM_op (s : Service) (o : Operation) : Real :=
  (FGS s o + DGS s o) / 2

/-- SGM: promedio de SGM_op sobre todas las operaciones -/
def SGM (s : Service) : Real :=
  if s.M = 0 then 0 else
  (s.ops.sum (SGM_op s)) / (Real.ofNat (s.M))

/-- NOO: número simple de operaciones (complejidad) -/
def NOO (s : Service) : Nat := s.M

end ServiceMetrics

/-
  Métrica de acoplamiento a nivel de sistema
-/
structure Call where
  from : String
  to   : String

/-- Coupling: número de destinos distintos que llama un servicio -/
def coupling (svcId : String) (calls : List Call) : Nat :=
  (calls.filter (·.from = svcId)).map (·.to).eraseDup.length

/-
  Invariantes arquitectónicos
-/
namespace Invariants

open ServiceMetrics

/-- No permitir llamadas RPC entre servicios no declarados -/
theorem noUndeclaredCalls (allowed : List (String × String)) (cs : List Call) :
  ∀ c ∈ cs, (c.from, c.to) ∈ allowed :=
by
  intros c hc
  -- aquí se usaría automatización o se reescribiría con `by_cases` según `allowed`
  admit

/-- Threshold de cohesión mínima: LCOM ≤ 0.8 -/
theorem cohesionThreshold (s : ServiceMetrics.Service) :
  ServiceMetrics.LCOM s ≤ 0.8 := by
  -- La demostración se basaría en asumir s.M > 0 ∧ s.F > 0 y cota de MF ≥ 0
  sorry

end Invariants
