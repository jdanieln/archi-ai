import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

/-!
  # ServiceMetrics
  Define las estructuras y métricas de calidad para evaluar diseños de microservicios.
-/

-- Estructura para una operación/método dentro de un servicio.
structure Operation where
  name   : String
  params : List String
  deriving Repr, BEq

-- Estructura para un servicio, que contiene un nombre y una lista de operaciones.
structure Service where
  name : String
  ops  : List Operation
  deriving Repr, BEq

-- Estructura para una llamada (dependencia) entre dos servicios.
structure Call where
  caller : String  -- El servicio que origina la llamada
  callee : String  -- El servicio que recibe la llamada
  deriving Repr, BEq

namespace ServiceMetrics

/--
  Calcula la Falta de Cohesión en Métodos (LCOM) para un servicio.
  Es `noncomputable` porque usa división de números reales.
-/
noncomputable def LCOM (s : Service) : Real :=
  let ops := s.ops
  if ops.length < 2 then 0.0 else
  let listOfLists := ops.map (fun o₁ => ops.map (fun o₂ => (o₁, o₂)))
  let allPairs := listOfLists.foldr List.append []
  let pairs := allPairs.filter (fun (o₁, o₂) => o₁.name < o₂.name)
  let (sharing, notSharing) := pairs.partition (fun (o₁, o₂) => o₁.params.any (fun p => o₂.params.contains p))
  let p := notSharing.length
  let q := sharing.length
  if p == 0 || q == 0 then 0.0 else
  (p : Real) / ((p : Real) + (q : Real))

/--
  Calcula la Granularidad Media del Servicio (SGM).
  Es simplemente el número de operaciones en el servicio.
-/
def SGM (s : Service) : Real :=
  s.ops.length

/--
  Calcula la desviación estándar de la granularidad de las operaciones (número de parámetros).
  Es `noncomputable` porque usa `Real.sqrt`.
-/
noncomputable def sgmSd (s : Service) : Real :=
  let n := s.ops.length
  if n == 0 then 0.0 else
  let paramsCount := s.ops.map (fun o => o.params.length)
  let mean := (paramsCount.foldl (· + ·) 0 : Real) / (n : Real)
  let variance := (paramsCount.map (fun c => ((c : Real) - mean)^2) |>.foldl (· + ·) 0) / (n : Real)
  Real.sqrt variance

/--
  Calcula el Acoplamiento de Salida (Fan-Out) para un servicio dado.
  Cuenta cuántos servicios *únicos* son llamados por el servicio `serviceName`.
-/
def couplingOut (serviceName : String) (calls : List Call) : Nat :=
  let targets := calls.filter (fun c => c.caller == serviceName) |>.map (·.callee)
  targets.eraseDups.length

end ServiceMetrics
