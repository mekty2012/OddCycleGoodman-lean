import OddCycleBound.IntermediateRegion.QuadraticBranch
import OddCycleBound.IntermediateRegion.Scalar.EnvelopeEstimates

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

namespace AdmissibleParams

variable (P : AdmissibleParams)

noncomputable def chartCxi : Real :=
  Real.sqrt (2 * P.alpha) * (1 + 4 * P.xi) / (2 + 4 * P.xi)

theorem chartCxi_pos : 0 < P.chartCxi := by
  unfold chartCxi
  apply div_pos
  · exact mul_pos (Real.sqrt_pos.2 (mul_pos (by norm_num) P.alpha_pos)) (by linarith [P.xi_pos])
  · linarith [P.xi_pos]

theorem f_eq_alpha_mul : P.f = P.alpha * (1 - P.ell) := by
  unfold f; rw [mul_sub, mul_one, P.alpha_mul_ell]

theorem d_eq_alpha_mul : P.d = P.alpha * P.chartU := by
  unfold d chartU; rw [mul_sub, mul_one, P.alpha_mul_tau]

theorem psi_ge_linear (h : 1 < 2 * P.rho * P.xi) :
    P.xi * (4 * P.xi + 1) / (4 * P.xi + 2) ≤ psi P.xi P.rho := by
  have hxi := P.xi_pos
  have hcross : 2 < 4 * P.xi * P.rho := by nlinarith [h, hxi, P.rho_pos]
  have hdenXi : 0 < 4 * P.xi + 2 := by linarith
  have hdenRho : 0 < 4 * (P.rho + 1) := by linarith [P.rho_pos]
  have htarget :
      P.xi * (4 * P.xi + 1) / (4 * P.xi + 2) ≤ P.xi - 1 / (4 * (P.rho + 1)) := by
    have hfrac : 1 / (4 * (P.rho + 1)) ≤ P.xi / (4 * P.xi + 2) := by
      rw [div_le_div_iff₀ hdenRho hdenXi]; nlinarith
    have hrewrite :
        P.xi * (4 * P.xi + 1) / (4 * P.xi + 2) = P.xi - P.xi / (4 * P.xi + 2) := by
      apply (div_eq_iff hdenXi.ne').2
      rw [sub_mul, div_mul_cancel₀ _ hdenXi.ne']; ring
    rw [hrewrite]; linarith
  exact htarget.trans (psi_ge_dual_one P.rho_pos.le)

theorem k_L_eq_chartKL : P.k P.L = P.alpha ^ P.chartN * P.chartKL := by
  have hm9 := P.m_ge_nine
  have hn1 : P.m - 1 = P.chartN + 1 := by unfold chartN; omega
  have hαpos := P.alpha_pos
  have hℓpos := P.ell_pos
  have hσℓ : (0 : Real) < P.chartSigma + P.ell := by
    have := P.chartSigma_pos; linarith [P.ell_pos]
  have hpL : (0 : Real) < P.p + P.L := add_pos P.p_pos P.L_pos
  have hαsucc : P.alpha ^ (P.chartN + 1) = P.alpha ^ P.chartN * P.alpha := pow_succ _ _
  have hσpow : P.chartSigma ^ (P.chartN + 1) = P.p ^ (P.chartN + 1) / P.alpha ^ (P.chartN + 1) := by
    unfold chartSigma; rw [div_pow]
  have hℓpow : P.ell ^ (P.chartN + 1) = P.L ^ (P.chartN + 1) / P.alpha ^ (P.chartN + 1) := by
    unfold ell; rw [div_pow]
  have hσℓadd : P.chartSigma + P.ell = (P.p + P.L) / P.alpha := by
    unfold chartSigma ell; field_simp
  unfold k chartKL
  rw [hn1, hσpow, hℓpow, hσℓadd, hαsucc]
  field_simp

theorem B_ge_m_mul : (P.m : Real) * (P.alpha ^ P.chartN * P.chartKL) ≤ P.B := by
  unfold B
  rw [show P.m - 2 = P.chartN by unfold chartN; rfl, ← P.k_L_eq_chartKL]
  have : (0 : Real) ≤ 2 * P.L ^ P.chartN := by
    have := pow_nonneg P.L_nonneg P.chartN; linarith
  linarith

theorem chartKL_ge : (P.chartSigma - P.ell) * P.chartSigma ^ (P.chartN - 1) ≤ P.chartKL := by
  have hcN7 : 7 ≤ P.chartN := by have := P.m_ge_nine; unfold chartN; omega
  have hσpos := P.chartSigma_pos
  have hℓpos := P.ell_pos
  have hσℓ : (0 : Real) < P.chartSigma + P.ell := by linarith
  have hℓσ : P.ell ≤ P.chartSigma := by
    have : P.ell < 1 := (P.ell_lt_tau).trans P.tau_lt_one
    linarith [P.chartSigma_gt_one]
  unfold chartKL
  rw [le_div_iff₀ hσℓ]

  have hσsplit : P.chartSigma ^ (P.chartN + 1) = P.chartSigma ^ 2 * P.chartSigma ^ (P.chartN - 1) := by
    rw [← pow_add]; congr 1; omega
  have hℓsplit : P.ell ^ (P.chartN + 1) = P.ell ^ 2 * P.ell ^ (P.chartN - 1) := by
    rw [← pow_add]; congr 1; omega
  have hℓσpow : P.ell ^ (P.chartN - 1) ≤ P.chartSigma ^ (P.chartN - 1) :=
    pow_le_pow_left₀ hℓpos.le hℓσ _
  rw [hσsplit, hℓsplit]
  nlinarith [mul_le_mul_of_nonneg_left hℓσpow (sq_nonneg P.ell), sq_nonneg P.ell,
    pow_nonneg hσpos.le (P.chartN - 1)]

theorem scalar_target_of_linear_core (h : 1 < 2 * P.rho * P.xi)
    (hcore : P.chartTN
      ≤ ((P.chartN : Real) + 2) * P.chartCxi * (1 - P.ell) * (P.chartSigma - P.ell)
          * P.chartSigma ^ (P.chartN - 1)) :
    P.R ≤ P.C * psi P.xi P.rho := by
  have hαpos := P.alpha_pos
  have hcxi := P.chartCxi_pos
  have hu := P.chartU_pos
  have hσℓpos : 0 < P.chartSigma - P.ell := by
    have : P.ell < 1 := (P.ell_lt_tau).trans P.tau_lt_one
    linarith [P.chartSigma_gt_one]
  have h1ℓpos : 0 < 1 - P.ell := by
    have : P.ell < 1 := (P.ell_lt_tau).trans P.tau_lt_one; linarith
  have hσpowpos : 0 < P.chartSigma ^ (P.chartN - 1) := pow_pos P.chartSigma_pos _

  have hwit := P.psi_ge_linear h
  have hCxi := P.C_mul_xi
  have hCwit : P.chartCxi * P.B * P.f * P.d ≤ P.C * psi P.xi P.rho := by
    have hstep : P.C * (P.xi * (4 * P.xi + 1) / (4 * P.xi + 2)) ≤ P.C * psi P.xi P.rho :=
      mul_le_mul_of_nonneg_left hwit P.C_pos.le
    have hid : P.C * (P.xi * (4 * P.xi + 1) / (4 * P.xi + 2)) = P.chartCxi * P.B * P.f * P.d := by
      have hden : (0 : Real) < 4 * P.xi + 2 := by linarith [P.xi_pos]
      rw [show P.C * (P.xi * (4 * P.xi + 1) / (4 * P.xi + 2))
          = (P.C * P.xi) * ((4 * P.xi + 1) / (4 * P.xi + 2)) by ring, hCxi]
      unfold chartCxi
      rw [show (2 : Real) + 4 * P.xi = 4 * P.xi + 2 by ring,
        show (1 : Real) + 4 * P.xi = 4 * P.xi + 1 by ring]
      field_simp
    linarith [hid ▸ hstep]

  have hf_eq := P.f_eq_alpha_mul
  have hd_eq := P.d_eq_alpha_mul
  have hBKL := P.B_ge_m_mul
  have hKL := P.chartKL_ge

  have hR2 : P.R ≤ P.alpha ^ P.m * (P.chartU * P.chartTN) := by
    rw [P.R_eq_alpha_pow_mul_chartFN]
    exact mul_le_mul_of_nonneg_left P.chartFN_le_chartU_mul_chartTN (pow_pos P.alpha_pos _).le

  have hαpow : P.alpha ^ P.m = P.alpha ^ P.chartN * P.alpha ^ 2 := by
    rw [← pow_add]; congr 1; have := P.m_ge_nine; unfold chartN; omega
  have hchain : P.alpha ^ P.m * (P.chartU * P.chartTN) ≤ P.chartCxi * P.B * P.f * P.d := by
    have hcoreU : P.chartU * P.chartTN
        ≤ P.chartU * (((P.chartN : Real) + 2) * P.chartCxi * (1 - P.ell) * (P.chartSigma - P.ell)
            * P.chartSigma ^ (P.chartN - 1)) := mul_le_mul_of_nonneg_left hcore hu.le

    have hBstep : P.chartCxi * (((P.m : Real)) * (P.alpha ^ P.chartN * P.chartKL)) * P.f * P.d
        ≤ P.chartCxi * P.B * P.f * P.d := by
      have hfd : (0 : Real) ≤ P.chartCxi * P.f * P.d := by
        have := P.f_pos; have := P.d_pos; positivity
      nlinarith [mul_le_mul_of_nonneg_left hBKL hcxi.le, P.f_pos, P.d_pos, hcxi]
    have hKLstep : P.chartCxi * ((P.m : Real) * (P.alpha ^ P.chartN
          * ((P.chartSigma - P.ell) * P.chartSigma ^ (P.chartN - 1)))) * P.f * P.d
        ≤ P.chartCxi * ((P.m : Real) * (P.alpha ^ P.chartN * P.chartKL)) * P.f * P.d := by
      have hm : (0 : Real) ≤ (P.m : Real) := by positivity
      have : (0 : Real) ≤ P.chartCxi * ((P.m : Real) * P.alpha ^ P.chartN) * P.f * P.d := by
        have := P.f_pos; have := P.d_pos; positivity
      nlinarith [mul_le_mul_of_nonneg_left hKL
        (show (0 : Real) ≤ P.chartCxi * ((P.m : Real) * P.alpha ^ P.chartN) * P.f * P.d by
          have := P.f_pos; have := P.d_pos; positivity)]

    have hEq : P.alpha ^ P.m * (P.chartU * (((P.chartN : Real) + 2) * P.chartCxi * (1 - P.ell)
          * (P.chartSigma - P.ell) * P.chartSigma ^ (P.chartN - 1)))
        = P.chartCxi * ((P.m : Real) * (P.alpha ^ P.chartN
            * ((P.chartSigma - P.ell) * P.chartSigma ^ (P.chartN - 1)))) * P.f * P.d := by
      rw [hαpow, hf_eq, hd_eq]
      have hmc : (P.m : Real) = (P.chartN : Real) + 2 := by
        have : P.m = P.chartN + 2 := by have := P.m_ge_nine; unfold chartN; omega
        rw [this]; push_cast; ring
      rw [hmc]; ring
    calc P.alpha ^ P.m * (P.chartU * P.chartTN)
        ≤ P.alpha ^ P.m * (P.chartU * (((P.chartN : Real) + 2) * P.chartCxi * (1 - P.ell)
            * (P.chartSigma - P.ell) * P.chartSigma ^ (P.chartN - 1))) :=
          mul_le_mul_of_nonneg_left hcoreU (pow_pos P.alpha_pos _).le
      _ = P.chartCxi * ((P.m : Real) * (P.alpha ^ P.chartN
            * ((P.chartSigma - P.ell) * P.chartSigma ^ (P.chartN - 1)))) * P.f * P.d := hEq
      _ ≤ P.chartCxi * ((P.m : Real) * (P.alpha ^ P.chartN * P.chartKL)) * P.f * P.d := hKLstep
      _ ≤ P.chartCxi * P.B * P.f * P.d := hBstep
  linarith [hR2, hchain, hCwit]

end AdmissibleParams

end OddCycleBound.IntermediateRegion.Scalar
