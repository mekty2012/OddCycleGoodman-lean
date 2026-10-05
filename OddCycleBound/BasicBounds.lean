import OddCycleBound.Necklace

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
theorem trace_compPow_nonneg (hW : IsGraphon W μ) (n : Nat) :
    0 <= trace μ (compPow μ W n) := by
  rw [trace]
  exact integral_nonneg fun x => compPow_nonneg hW n x x

omit [IsProbabilityMeasure μ] in
/-- For `p ≤ 1/2` the right-hand side `p^m - p (1-p)^(m-1)` of Theorem 1.1 is nonpositive. -/
theorem rhs_nonpos_of_le_half (hW : IsGraphon W μ) {m : ℕ} (hm : 1 ≤ m)
    (hp : edgeDensity W μ ≤ 1 / 2) :
    edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) ≤ 0 := by
  have hp0 : 0 ≤ edgeDensity W μ := edgeDensity_nonneg hW
  have hpow : edgeDensity W μ ^ (m - 1) ≤ (1 - edgeDensity W μ) ^ (m - 1) :=
    pow_le_pow_left₀ hp0 (by linarith) (m - 1)
  have hsplit : edgeDensity W μ ^ m = edgeDensity W μ * edgeDensity W μ ^ (m - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hm]
  rw [hsplit, ← mul_sub]
  exact mul_nonpos_of_nonneg_of_nonpos hp0 (by linarith)

end OddCycleBound
