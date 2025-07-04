import Lake
open Lake DSL

package «alpha_pipeline» {
  -- Le decimos a Lake que las fuentes están en la subcarpeta "Formal"
  srcDir := "Formal"
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
  @ "main"

-- Biblioteca de métricas (ServiceMetrics.lean)
lean_lib ServiceMetrics

-- Ejecutable de validación (ValidateGenotype.lean)
@[default_target]
lean_exe verifyGenotype where
  root := `ValidateGenotype
