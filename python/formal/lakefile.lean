import Lake
open Lake DSL

package formal

lean_lib Formal

lean_exe formal {
  root := `Formal.ValidateGenotype
}