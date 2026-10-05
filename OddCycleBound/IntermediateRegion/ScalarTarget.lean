import OddCycleBound.IntermediateRegion.LinearLowZeta
import OddCycleBound.IntermediateRegion.LinearN7Mid
import OddCycleBound.IntermediateRegion.LinearHighZeta
import OddCycleBound.IntermediateRegion.LinearBroad
import OddCycleBound.IntermediateRegion.QuadraticBranch

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

namespace AdmissibleParams

variable (P : AdmissibleParams)

theorem linear_core :
    P.chartTN ≤ ((P.chartN : ℝ) + 2) * P.chartCxi * (1 - P.ell) * (P.chartSigma - P.ell)
      * P.chartSigma ^ (P.chartN - 1) := by
  by_cases hv : 5 / 8 ≤ P.chartV
  · exact P.linear_large_v hv
  · push Not at hv
    by_cases hN9 : 9 ≤ P.chartN
    · by_cases hζ : (P.chartN : ℝ) ≤ P.chartZeta
      · exact P.linear_high_zeta hζ (le_of_lt hv)
      · exact P.linear_low_zeta hN9 (le_of_lt (not_le.mp hζ))
    · have hN7 : P.chartN = 7 := by
        obtain ⟨t, ht⟩ := P.m_odd
        have hm := P.m_ge_nine
        have hlt : P.chartN < 9 := not_le.mp hN9
        unfold chartN at hlt ⊢; omega
      by_cases hζ7 : P.chartZeta ≤ 7
      · by_cases hv14 : P.chartV ≤ 1 / 4
        · exact P.linear_N7_small_v hN7 hζ7 hv14
        · exact P.linear_N7_middle_v hN7 hζ7 (le_of_lt (not_le.mp hv14)) (le_of_lt hv)
      · exact P.linear_high_zeta (by rw [hN7]; push_cast; linarith [not_le.mp hζ7]) (le_of_lt hv)

theorem scalar_target : P.R ≤ P.C * psi P.xi P.rho := by
  by_cases h : 2 * P.rho * P.xi ≤ 1
  · exact P.quadratic_branch h
  · exact P.scalar_target_of_linear_core (not_le.mp h) P.linear_core

end AdmissibleParams

end OddCycleBound.IntermediateRegion.Scalar
