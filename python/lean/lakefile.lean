import Lake
open Lake DSL

package «alpha_pipeline» { }

-- tu librería de métricas
lean_lib ServiceMetrics

-- ejecutable que vamos a invocar desde Python
lean_exe verifyGenotype where
  root := `ValidateGenotype
