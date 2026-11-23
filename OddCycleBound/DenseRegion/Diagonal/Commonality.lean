import OddCycleBound.DenseRegion.Diagonal.DenseRegionEndgame

open MeasureTheory

namespace OddCycleBound.DenseRegion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {W : Ω → Ω → ℝ}

theorem neckSum_ge_baseline_unconditional {m : ℕ} (hW : IsGraphon W μ)
    (hp : 2 / 3 ≤ edgeDensity W μ) (hm : Odd m) (hm3 : 3 ≤ m) :
    edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) ≤
      neckSum W μ m :=
  neckSum_ge_baseline_of_diagKernel_nonneg hW hm hm3 fun _ hr _ hell =>
    diagKernel_nonneg_uniform diagKernelPosEll_unconditional hm hr.1 hr.2
      (by linarith [edgeDensity_le_one hW]) (by linarith) hell

/-- The inequality of **Theorem 1.2** (strengthened extended commonality) for `p ≥ 2/3`. -/
theorem dense_region_commonality_bound {m : ℕ} (hW : IsGraphon W μ)
    (hp : 2 / 3 ≤ edgeDensity W μ) (hm : Odd m) (hm3 : 3 ≤ m) :
    cycleDensity μ W m + cycleDensity μ (compl W) m ≥
      edgeDensity W μ ^ m + (1 - edgeDensity W μ) ^ m +
        (pathDensity (compl W) μ (m - 1) - (1 - edgeDensity W μ) ^ (m - 1)) :=
  commonality_of_neckSum_ge hW hm hm3 (neckSum_ge_baseline_unconditional hW hp hm hm3)

end OddCycleBound.DenseRegion
