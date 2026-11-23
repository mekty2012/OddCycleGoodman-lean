import OddCycleBound.DenseRegion.Expansion
import OddCycleBound.DenseRegion.GraphonReduction
import OddCycleBound.DenseRegion.GraphonKrylovBridge
import OddCycleBound.DenseRegion.Excursion.Reduction

open MeasureTheory

namespace OddCycleBound.DenseRegion

variable {Omega : Type*} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega → Omega → ℝ}
variable {ι : Type*} [Fintype ι]

theorem neckSum_ge_baseline_of_diagKernel_nonneg {m : ℕ} (hW : IsGraphon W mu)
    (hm : Odd m) (hm3 : 3 ≤ m)
    (hdiag : ∀ r, 1 ≤ r ∧ 2 * r < m →
      ∀ ell ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2),
        0 ≤ diagKernel m r (1 - edgeDensity W mu) ell) :
    edgeDensity W mu ^ m - edgeDensity W mu * (1 - edgeDensity W mu) ^ (m - 1) ≤
      neckSum W mu m := by
  rw [neckSum_eq_baseline_add_momentPhi hW hm hm3]
  linarith [momentPhi_specMoment_nonneg hm hm3 (isGraphon_compl hW)
    (1 - edgeDensity W mu) hdiag]

/-- Lemma 4.3 and the comparison after Theorem 1.2, assuming the pointwise nonnegativity of the
excursion polynomials. -/
theorem neckSum_ge_baseline_of_multiKernel_nonneg {m : ℕ} (hW : IsGraphon W mu)
    (hm : Odd m) (hm3 : 3 ≤ m)
    (hP : ∀ r, 1 ≤ r ∧ 2 * r < m → ∀ L : List ℝ, L.length = r →
      (∀ x ∈ L, x ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) →
        0 ≤ multiKernel m r (1 - edgeDensity W mu) L) :
    edgeDensity W mu ^ m - edgeDensity W mu * (1 - edgeDensity W mu) ^ (m - 1) ≤
      neckSum W mu m := by
  rw [neckSum_eq_baseline_add_momentPhi hW hm hm3]
  linarith [momentPhi_specMoment_nonneg' hm hm3 (isGraphon_compl hW)
    (1 - edgeDensity W mu) hP]

theorem cycle_bound_of_diagKernel_nonneg {m : ℕ} (hW : IsGraphon W mu)
    (hm : Odd m) (hm3 : 3 ≤ m)
    (hdiag : ∀ r, 1 ≤ r ∧ 2 * r < m →
      ∀ ell ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2),
        0 ≤ diagKernel m r (1 - edgeDensity W mu) ell) :
    edgeDensity W mu ^ m - edgeDensity W mu * (1 - edgeDensity W mu) ^ (m - 1) ≤
      cycleDensity mu W m :=
  cycle_bound_of_neckSum hW hm hm3
    (neckSum_ge_baseline_of_diagKernel_nonneg hW hm hm3 hdiag)

end OddCycleBound.DenseRegion
