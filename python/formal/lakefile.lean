import Lake
open Lake DSL

package «alpha_pipeline» {
  srcDir := "Formal"
}

-- Dependencias alineadas con Lean 4.22.0-rc3 (usando 'main' para la última compatibilidad)
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
  @ "master" -- La rama 'main' de Mathlib suele estar alineada con la última RC/estable de Lean

require aesop from git
  "https://github.com/leanprover-community/aesop"
  @ "master" -- La rama 'main' de Aesop suele estar alineada con la última RC/estable de Lean

require batteries from git
  "https://github.com/leanprover-community/batteries"
  @ "main" -- La rama 'main' de Batteries suele estar alineada con la última RC/estable de Lean

require proofwidgets from git
  "https://github.com/leanprover-community/ProofWidgets4.git"
  @ "main" -- La rama 'main' de ProofWidgets4 suele estar alineada con la última RC/estable de Lean

require importGraph from git
  "https://github.com/leanprover-community/import-graph"
  @ "main" -- La rama 'main' de ImportGraph suele estar alineada con la última RC/estable de Lean

-- Biblioteca de métricas (ServiceMetrics.lean)
lean_lib ServiceMetrics

-- Ejecutable de validación (ValidateGenotype.lean)
@[default_target]
lean_exe verifyGenotype where
  root := `ValidateGenotype