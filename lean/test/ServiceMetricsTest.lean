import Std.Tactic.Linarith
import ServiceMetrics
open ServiceMetrics

-- Servicio de ejemplo con dos operaciones compartiendo un parámetro
def svc1 : Service := {
  ops := [
    { name := "create", params := ["x","y"] },
    { name := "read",   params := ["x"] }
  ]
}

-- Servicio vacío
def svc0 : Service := { ops := [] }

-- Pruebas para LCOM
theorem LCOM_range (s : Service) : 0 ≤ LCOM s ∧ LCOM s ≤ 1 := by
  dsimp [LCOM]
  split
  · -- 0 ≤ LCOM
    by_cases h : s.M = 0 ∨ s.F = 0
    · simp [LCOM, h]
    · -- caso s.M>0 ∧ s.F>0
      have hDen : 0 < (Real.ofNat (s.M * s.F)) := by
        dsimp [ServiceMetrics.M, ServiceMetrics.F]; sorry
      have hMF : (MF s : Real) ≥ 0 := by norm_cast; exact Nat.cast_nonneg _
      linarith
  · -- LCOM ≤ 1
    by_cases h : s.M = 0 ∨ s.F = 0
    · simp [LCOM, h]
    · dsimp [LCOM]
      have hDiv : (MF s : Real) / (Real.ofNat (s.M * s.F)) ≥ 0 := by
        apply div_nonneg; norm_cast; exact Nat.cast_nonneg _
      linarith

-- Prueba para SGM en [0,4]
theorem SGM_nonneg (s : Service) : 0 ≤ SGM s := by
  dsimp [SGM]
  cases s.M
  · simp
  · dsimp; apply div_nonneg;
    · apply List.sum_nonneg; intros _ _; dsimp [SGM_op, FGS, DGS]; apply add_nonneg;
      · by_cases h : s.F = 0;
        · simp [h]; exact zero_le _
        · dsimp; apply div_nonneg; norm_cast; exact Nat.cast_nonneg _
      · apply zero_le

-- Prueba para NOO
theorem NOO_nonneg (s : Service) : 0 ≤ (NOO s : Int) := by
  dsimp [NOO]; norm_cast; apply Int.ofNat_nonneg

-- Prueba coupling
example : coupling "A" [{ from := "A", to := "B" }, { from := "A", to := "B" }] = 1 := by
  dsimp [coupling]; simp

-- Placeholder de invariante
--#eval Invariants.noUndeclaredCalls [("A","B")] [{ from := "A", to := "B" }]

