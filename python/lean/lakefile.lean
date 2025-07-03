-- lean/lakefile.lean
import Lake
open Lake DSL

package alpha_pipeline {
    srcDir := "src"
}

-- dependemos de mathlib4 para Real, sqrt, etc.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
  @ "main"

-- 1) Biblioteca de métricas: Lake buscará src/ServiceMetrics.lean
lean_lib ServiceMetrics

-- 2) Ejecutable de validación: Lake buscará src/ValidateGenotype.lean
@[default_target]
lean_exe verifyGenotype where
  root     := `ValidateGenotype
