import OddCycleBound.IntermediateRegion.Scalar.ThreeGeometric
import OddCycleBound.IntermediateRegion.DirectedKernel

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar
namespace AdmissibleParams

variable (P : AdmissibleParams)

theorem k_eq_directedKernel (lambda : Real) (hlambda : -P.p <= lambda)
    (hden : P.p + lambda ≠ 0) :
    P.k lambda = IntermediateRegion.directedKernel P.p P.m lambda := by
  unfold k
  symm
  exact IntermediateRegion.directedKernel_eq_div P.m_odd
    (le_trans (by norm_num) P.m_ge_nine) hlambda hden

theorem C_mul_xi :
    P.C * P.xi = Real.sqrt (2 * P.alpha) * P.B * P.f * P.d := by
  unfold C xi
  have he : P.e ≠ 0 := P.e_pos.ne'
  have ha : P.alpha ≠ 0 := P.alpha_pos.ne'
  field_simp [he, ha]

end AdmissibleParams
end OddCycleBound.IntermediateRegion.Scalar
