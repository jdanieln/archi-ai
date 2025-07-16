-- import Mathlib.Data.Real.Basic -- Se puede mantener por si se usa en otro lado, pero no para Float.

/-!
  # ServiceMetrics (Versión 100% Computable)
  Métricas de calidad usando Float para la computación.
-/

-- Las estructuras no cambian
structure Operation where
  name   : String
  params : List String
  deriving Repr, BEq

structure Service where
  name : String
  ops  : List Operation
  deriving Repr, BEq

structure Call where
  caller : String
  callee : String
  deriving Repr, BEq

namespace ServiceMetrics

/--
  Calcula LCOM usando Float. Ahora es computable.
-/
def LCOM (s : Service) : Float :=
  let ops := s.ops
  if ops.length < 2 then 0.0 else
  let listOfLists := ops.map (fun o₁ => ops.map (fun o₂ => (o₁, o₂)))
  let allPairs := listOfLists.foldr List.append []
  let pairs := allPairs.filter (fun (o₁, o₂) => o₁.name < o₂.name)
  let (sharing, notSharing) := pairs.partition (fun (o₁, o₂) => o₁.params.any (fun p => o₂.params.contains p))
  let p := Float.ofNat notSharing.length
  let q := Float.ofNat sharing.length
  if p == 0.0 || q == 0.0 then 0.0 else
  p / (p + q)

/--
  Calcula SGM usando Float.
-/
def SGM (s : Service) : Float :=
  Float.ofNat s.ops.length

/--
  Calcula la desviación estándar de la granularidad usando Float.
-/
def sgmSd (s : Service) : Float :=
  let n_nat := s.ops.length
  if n_nat == 0 then 0.0 else
  let n := Float.ofNat n_nat
  let paramsCount := s.ops.map (fun o => Float.ofNat o.params.length)
  let mean := (paramsCount.foldl (· + ·) 0.0) / n
  let variance := (paramsCount.map (fun c => (c - mean)^2) |>.foldl (· + ·) 0.0) / n
  Float.sqrt variance

/--
  Calcula el Fan-Out. Esta función ya era computable.
-/
def couplingOut (serviceName : String) (calls : List Call) : Nat :=
  let targets := calls.filter (fun c => c.caller == serviceName) |>.map (·.callee)
  targets.eraseDups.length

end ServiceMetrics
