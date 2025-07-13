import Lake
open Lake DSL

package formal { }
-- Biblioteca de métricas (busca Src/ServiceMetrics.lean)
lean_lib ServiceMetrics

-- Ejecutable de validación (busca Src/ValidateGenotype.lean)
@[default_target]
lean_exe validateGenotype where
  root     := `ValidateGenotype
