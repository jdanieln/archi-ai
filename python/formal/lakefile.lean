import Lake
open Lake DSL

package formal { }

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
  @ "master"
-- Biblioteca de métricas (busca Src/ServiceMetrics.lean)
lean_lib ServiceMetrics

-- Ejecutable de validación (busca Src/ValidateGenotype.lean)
@[default_target]
lean_exe validateGenotype where
  root     := `ValidateGenotype
