import OddCycleBound.IntermediateRegion.ShiftSpectral
import OddCycleBound.IntermediateRegion.Scalar.Definitions

open MeasureTheory

noncomputable section

namespace OddCycleBound.IntermediateRegion

open OddCycleBound.DenseRegion

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega -> Omega -> Real}

theorem graphon_leading_eigenvalue_defect_lower_bound_directed
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    {m : Nat} (hp : 1 / 2 < edgeDensity W mu)
    (hm : Odd m) (hm3 : 3 <= m) :
    let p := edgeDensity W mu
    let q := 1 - p
    let alpha := complementEigenvalue hW i
    let L := leadingEigenvalueSafeRadius hW i
    let phi := centeredEigenmode hW i
    let g := centeredDegreeL2 hW
    let c := inner Real g phi
    let gs := g - c • phi
    (-(alpha ^ m + L ^ m - p * q ^ (m - 1)) +
        (2 * L ^ (m - 2) +
          (m : Real) * directedKernel p m alpha) * c ^ 2 +
        (2 * L ^ (m - 2) +
          (m : Real) * directedKernel p m L) * ‖gs‖ ^ 2 <=
      cycleDensity mu W m - (p ^ m - p * q ^ (m - 1))) := by
  dsimp only
  let p := edgeDensity W mu
  let q := 1 - p
  let alpha := complementEigenvalue hW i
  let L := leadingEigenvalueSafeRadius hW i
  let phi := centeredEigenmode hW i
  let g := centeredDegreeL2 hW
  let c := inner Real g phi
  let gs := g - c • phi
  have hphiNorm : ‖phi‖ = 1 :=
    (centeredEigenmode_orthonormal hW).norm_eq_one i
  have horthGS : inner Real gs phi = 0 := by
    dsimp [gs, c]
    rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq,
      hphiNorm]
    simp
  have horth : inner Real (c • phi) gs = 0 := by
    rw [real_inner_smul_left, real_inner_comm, horthGS]
    simp
  have hdecomp : g = c • phi + gs := by
    dsimp [gs]
    abel
  have hnorm : ‖g‖ ^ 2 = c ^ 2 + ‖gs‖ ^ 2 := by
    calc
      ‖g‖ ^ 2 = ‖c • phi + gs‖ ^ 2 := by rw [hdecomp]
      _ = ‖c • phi‖ ^ 2 + ‖gs‖ ^ 2 :=
        by simpa [pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_real horth
      _ = c ^ 2 + ‖gs‖ ^ 2 := by
        simp [norm_smul, Real.norm_eq_abs, hphiNorm, sq_abs]
  have htrace := centered_trace_leading_eigenvalue_defect_lower_bound
    hW i hm hm3
  have hshift := graphonOneSidedShift_leading_eigenvalue_lower_bound
    hW i hp hm (by omega)
  have hid := graphon_oneSidedShift_identity hW (by omega : 0 < m)
  dsimp only at htrace hshift hid
  calc
    -(alpha ^ m + L ^ m - p * q ^ (m - 1)) +
          (2 * L ^ (m - 2) +
            (m : Real) * directedKernel p m alpha) * c ^ 2 +
          (2 * L ^ (m - 2) +
            (m : Real) * directedKernel p m L) * ‖gs‖ ^ 2 =
        (-alpha ^ m - L ^ m +
            2 * L ^ (m - 2) * ‖g‖ ^ 2) +
          (m : Real) *
            (directedKernel p m alpha * c ^ 2 +
              directedKernel p m L * ‖gs‖ ^ 2) +
          p * q ^ (m - 1) := by
            rw [hnorm]
            ring
    _ <= trace mu (compPow mu (centeredKernel W mu) (m - 1)) +
          graphonOneSidedShift hW m + p * q ^ (m - 1) := by
            linarith
    _ = cycleDensity mu W m - (p ^ m - p * q ^ (m - 1)) := by
          rw [hid]
          dsimp [p]
          ring

end OddCycleBound.IntermediateRegion
