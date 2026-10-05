import OddCycleBound.DenseRegion.Diagonal.GammaMomentProof
import OddCycleBound.DenseRegion.Diagonal.GammaSmoothing
import OddCycleBound.DenseRegion.Diagonal.Positivity

open MeasureTheory

namespace OddCycleBound.DenseRegion

theorem diagKernelPosEll_unconditional : DiagKernelPosEll :=
  diagKernel_nonneg_pos_ell gamma_moment_inequality

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {W : Ω → Ω → ℝ}

theorem dense_region_cycle_bound_unconditional
    {m : ℕ} (hW : IsGraphon W μ) (hp : 2 / 3 ≤ edgeDensity W μ) (hm : Odd m) (hm3 : 3 ≤ m) :
    edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) ≤
      cycleDensity μ W m :=
  dense_region_cycle_bound diagKernelPosEll_unconditional hW hp hm hm3

end OddCycleBound.DenseRegion
