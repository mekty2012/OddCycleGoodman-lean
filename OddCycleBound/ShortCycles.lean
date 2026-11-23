import OddCycleBound.ShortCycles.ExcursionPolynomials
import OddCycleBound.DenseRegion.ExpansionAssembly
import OddCycleBound.BasicBounds

/-!
# The cycles `C_3`, `C_5`, `C_7` (Section 5)

For `m ∈ {3, 5, 7}` every excursion polynomial `P_{m,r}(q; ·)` is pointwise nonnegative when
`q = 1 - p ≤ 1/2` (Proposition 5.1, `multiKernel_nonneg_short`). Lemma 4.3 then gives
Theorem 1.2 and Theorem 1.1 for these cycles throughout `p ≥ 1/2`. For `p ≤ 1/2` the bound of
Theorem 1.1 is trivial.
-/

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {W : Ω → Ω → ℝ}

lemma odd_of_short {m : ℕ} (hm : m = 3 ∨ m = 5 ∨ m = 7) : Odd m ∧ 3 ≤ m := by
  rcases hm with rfl | rfl | rfl
  exacts [⟨⟨1, rfl⟩, le_rfl⟩, ⟨⟨2, rfl⟩, by norm_num⟩, ⟨⟨3, rfl⟩, by norm_num⟩]

lemma neckSum_ge_baseline_short {m : ℕ} (hW : IsGraphon W μ) (hm : m = 3 ∨ m = 5 ∨ m = 7)
    (hp : 1 / 2 ≤ edgeDensity W μ) :
    edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) ≤
      DenseRegion.neckSum W μ m :=
  DenseRegion.neckSum_ge_baseline_of_multiKernel_nonneg hW (odd_of_short hm).1
    (odd_of_short hm).2 fun _ hr L hlen _ =>
      multiKernel_nonneg_short hm hr.1 hr.2 (by linarith [edgeDensity_le_one hW]) (by linarith)
        L hlen

/-- **Proposition 5.1, consequence for Theorem 1.2:** strengthened extended commonality for
`m ∈ {3, 5, 7}` and `p ≥ 1/2`. -/
theorem commonality_short {m : ℕ} (hW : IsGraphon W μ) (hm : m = 3 ∨ m = 5 ∨ m = 7)
    (hp : 1 / 2 ≤ edgeDensity W μ) :
    cycleDensity μ W m + cycleDensity μ (compl W) m ≥
      edgeDensity W μ ^ m + (1 - edgeDensity W μ) ^ m +
        (pathDensity (compl W) μ (m - 1) - (1 - edgeDensity W μ) ^ (m - 1)) :=
  DenseRegion.commonality_of_neckSum_ge hW (odd_of_short hm).1 (odd_of_short hm).2
    (neckSum_ge_baseline_short hW hm hp)

/-- **Proposition 5.1, consequence for Theorem 1.1:** the odd-cycle Goodman bound for
`m ∈ {3, 5, 7}` and `p ≥ 1/2`. -/
theorem cycle_bound_short {m : ℕ} (hW : IsGraphon W μ) (hm : m = 3 ∨ m = 5 ∨ m = 7)
    (hp : 1 / 2 ≤ edgeDensity W μ) :
    cycleDensity μ W m ≥
      edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) :=
  DenseRegion.cycle_bound_of_neckSum hW (odd_of_short hm).1 (odd_of_short hm).2
    (neckSum_ge_baseline_short hW hm hp)

/-- The odd-cycle Goodman bound for `m ∈ {3, 5, 7}` at every edge density. -/
theorem cycle_bound_short_all {m : ℕ} (hW : IsGraphon W μ) (hm : m = 3 ∨ m = 5 ∨ m = 7) :
    cycleDensity μ W m ≥
      edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) := by
  by_cases hp : 1 / 2 ≤ edgeDensity W μ
  · exact cycle_bound_short hW hm hp
  · have hnonneg : 0 ≤ cycleDensity μ W m := trace_compPow_nonneg hW (m - 1)
    have := rhs_nonpos_of_le_half hW (m := m) (by have := (odd_of_short hm).2; omega)
      (by linarith)
    linarith

end OddCycleBound
