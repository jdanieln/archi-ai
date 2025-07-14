import Lake
open Lake DSL

package formal

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

lean_lib ServiceMetrics where
  srcDir := "src"

@[default_target]
lean_exe validate where
  root := `ValidateGenotype
  srcDir := "src"
