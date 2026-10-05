import OddCycleBound.Necklace

/-!
# Regular graphons and the spectral step of Proposition 6.2

For an a.e. `q`-regular graphon `U` we prove, without eigenvalues, the facts used in the proof of
Proposition 6.2: `t(P_k, U) = q^k`, and the Hilbert–Schmidt version of the operator-norm bound
`‖T_U‖ ≤ q`, namely `‖U ∘ K‖_HS ≤ q ‖K‖_HS`. With `m = 2a + 1`, the cycle density
`t(C_m, U)` is the Hilbert–Schmidt pairing of the `a`-fold and `(a+1)`-fold kernel powers, and the
chain `t(C_m, U) ≤ q^{m-2} ∫∫ U² ≤ q^{m-1}` together with its equality cases gives `U ∈ {0,1}` and
`∫ U(x,z) U(z,y) dz = q U(x,y)` almost everywhere (equation `eq:equal-neighbourhoods`).
-/

open MeasureTheory

namespace OddCycleBound.Equality

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The Hilbert–Schmidt pairing `∫∫ K L` of two kernels. -/
noncomputable def hsInner (μ : Measure Ω) (K L : Ω → Ω → ℝ) : ℝ :=
  ∫ p, K p.1 p.2 * L p.1 p.2 ∂(μ.prod μ)

lemma _root_.OddCycleBound.GoodK.integrable_mul {K L : Ω → Ω → ℝ} (hK : GoodK K) (hL : GoodK L) :
    Integrable (fun p : Ω × Ω => K p.1 p.2 * L p.1 p.2) (μ.prod μ) := by
  obtain ⟨CK, _, hCK⟩ := hK.bdd
  obtain ⟨CL, _, hCL⟩ := hL.bdd
  refine (integrable_const (CK * CL)).mono' (hK.meas.mul hL.meas).aestronglyMeasurable
    (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hCK _ _) (hCL _ _) (abs_nonneg _) (le_trans (abs_nonneg _) (hCK p.1 p.2))

omit [IsProbabilityMeasure μ] in
lemma goodK_sub_smul {A B : Ω → Ω → ℝ} (hA : GoodK A) (hB : GoodK B) (c : ℝ) :
    GoodK (fun x y => A x y - c * B x y) := by
  obtain ⟨CA, hCA0, hCA⟩ := hA.bdd
  obtain ⟨CB, hCB0, hCB⟩ := hB.bdd
  refine ⟨hA.meas.sub (hB.meas.const_mul c), ⟨CA + |c| * CB, by positivity, fun x y => ?_⟩⟩
  calc |A x y - c * B x y| ≤ |A x y| + |c * B x y| := abs_sub _ _
    _ ≤ CA + |c| * CB := by
        rw [abs_mul]
        exact add_le_add (hCA x y) (mul_le_mul_of_nonneg_left (hCB x y) (abs_nonneg c))

omit [IsProbabilityMeasure μ] in
lemma hsInner_self_nonneg (K : Ω → Ω → ℝ) : 0 ≤ hsInner μ K K :=
  integral_nonneg fun _ => mul_self_nonneg _

lemma hsInner_sub_smul_self {A B : Ω → Ω → ℝ} (hA : GoodK A) (hB : GoodK B) (c : ℝ) :
    hsInner μ (fun x y => A x y - c * B x y) (fun x y => A x y - c * B x y) =
      hsInner μ A A - 2 * c * hsInner μ A B + c ^ 2 * hsInner μ B B := by
  unfold hsInner
  have e : ∀ p : Ω × Ω, (A p.1 p.2 - c * B p.1 p.2) * (A p.1 p.2 - c * B p.1 p.2) =
      A p.1 p.2 * A p.1 p.2 - 2 * c * (A p.1 p.2 * B p.1 p.2) +
        c ^ 2 * (B p.1 p.2 * B p.1 p.2) := fun p => by ring
  simp_rw [e]
  have h1 : Integrable (fun p : Ω × Ω => A p.1 p.2 * A p.1 p.2) (μ.prod μ) :=
    hA.integrable_mul hA
  have h2 : Integrable (fun p : Ω × Ω => 2 * c * (A p.1 p.2 * B p.1 p.2)) (μ.prod μ) :=
    (hA.integrable_mul hB).const_mul _
  have h3 : Integrable (fun p : Ω × Ω => c ^ 2 * (B p.1 p.2 * B p.1 p.2)) (μ.prod μ) :=
    (hB.integrable_mul hB).const_mul _
  have h12 : Integrable (fun p : Ω × Ω =>
      A p.1 p.2 * A p.1 p.2 - 2 * c * (A p.1 p.2 * B p.1 p.2)) (μ.prod μ) := h1.sub h2
  rw [integral_add h12 h3, integral_sub h1 h2, integral_const_mul, integral_const_mul]

lemma hsInner_sub_left {A B C : Ω → Ω → ℝ} (hA : GoodK A) (hB : GoodK B) (hC : GoodK C)
    (c : ℝ) :
    hsInner μ C (fun x y => A x y - c * B x y) = hsInner μ C A - c * hsInner μ C B := by
  unfold hsInner
  have e : ∀ p : Ω × Ω, C p.1 p.2 * (A p.1 p.2 - c * B p.1 p.2) =
      C p.1 p.2 * A p.1 p.2 - c * (C p.1 p.2 * B p.1 p.2) := fun p => by ring
  simp_rw [e]
  have h1 : Integrable (fun p : Ω × Ω => C p.1 p.2 * A p.1 p.2) (μ.prod μ) :=
    hC.integrable_mul hA
  have h2 : Integrable (fun p : Ω × Ω => c * (C p.1 p.2 * B p.1 p.2)) (μ.prod μ) :=
    (hC.integrable_mul hB).const_mul _
  rw [integral_sub h1 h2, integral_const_mul]

/-- Cauchy–Schwarz for the Hilbert–Schmidt pairing. -/
lemma hsInner_sq_le {A B : Ω → Ω → ℝ} (hA : GoodK A) (hB : GoodK B) :
    hsInner μ A B ^ 2 ≤ hsInner μ A A * hsInner μ B B := by
  have h : ∀ t : ℝ,
      0 ≤ hsInner μ B B * (t * t) + (-2 * hsInner μ A B) * t + hsInner μ A A := by
    intro t
    have := hsInner_self_nonneg (μ := μ) (fun x y => A x y - t * B x y)
    rw [hsInner_sub_smul_self hA hB t] at this
    nlinarith [this]
  have hd := discrim_le_zero h
  unfold discrim at hd
  nlinarith [hd]

lemma hsInner_eq_zero_of_self_eq_zero {A B : Ω → Ω → ℝ} (hA : GoodK A) (hB : GoodK B)
    (h : hsInner μ B B = 0) : hsInner μ A B = 0 := by
  have := hsInner_sq_le (μ := μ) hA hB
  rw [h, mul_zero] at this
  exact pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm this (sq_nonneg _))

lemma ae_eq_zero_of_hsInner_self_eq_zero {A : Ω → Ω → ℝ} (hA : GoodK A)
    (h : hsInner μ A A = 0) : ∀ᵐ p ∂(μ.prod μ), A p.1 p.2 = 0 := by
  unfold hsInner at h
  rw [integral_eq_zero_iff_of_nonneg (fun p => mul_self_nonneg _) (hA.integrable_mul hA)] at h
  filter_upwards [h] with p hp
  exact mul_self_eq_zero.mp hp

/-- The trace of a product is the Hilbert–Schmidt pairing when the second factor is symmetric. -/
lemma trace_comp_eq_hsInner {A B : Ω → Ω → ℝ} (hA : GoodK A) (hB : GoodK B)
    (hBs : ∀ x y, B x y = B y x) : trace μ (comp μ A B) = hsInner μ A B := by
  unfold trace comp hsInner
  rw [integral_prod _ (hA.integrable_mul hB)]
  refine integral_congr_ae (ae_of_all _ fun x => integral_congr_ae (ae_of_all _ fun z => ?_))
  simp only [hBs z x]

lemma comp_compPow_compPow {U : Ω → Ω → ℝ} (hU : GoodK U) : ∀ a b : ℕ,
    comp μ (compPow μ U a) (compPow μ U b) = compPow μ U (a + b + 1)
  | 0, b => by rw [show 0 + b + 1 = b + 1 by omega]; rfl
  | a + 1, b => by
      show comp μ (comp μ U (compPow μ U a)) (compPow μ U b) = _
      rw [comp_assoc hU (goodK_compPow hU a) (goodK_compPow hU b), comp_compPow_compPow hU a b,
        show a + 1 + b + 1 = (a + b + 1) + 1 by omega]
      rfl

/-- `⟨U^{a+1}, U^{b+1}⟩_HS = t(C_{a+b+2}, U)` for a graphon `U`. -/
lemma hsInner_compPow {U : Ω → Ω → ℝ} (hU : IsGraphon U μ) (a b : ℕ) :
    hsInner μ (compPow μ U a) (compPow μ U b) = trace μ (compPow μ U (a + b + 1)) := by
  have hGU := goodK_of_isGraphon hU
  rw [← comp_compPow_compPow hGU a b,
    trace_comp_eq_hsInner (goodK_compPow hGU a) (goodK_compPow hGU b)
      (compPow_symm hGU hU.symm b)]

/-! ### Regular graphons -/

variable {U : Ω → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
lemma pathIter_ae_eq_of_regular (hU : IsGraphon U μ) {q : ℝ}
    (hdeg : ∀ᵐ x ∂μ, degree U μ x = q) : ∀ k : ℕ, ∀ᵐ x ∂μ, pathIter U μ k x = q ^ k
  | 0 => ae_of_all _ fun _ => by simp [pathIter]
  | k + 1 => by
      have ih := pathIter_ae_eq_of_regular hU hdeg k
      filter_upwards [hdeg] with x hx
      show ∫ y, U x y * pathIter U μ k y ∂μ = q ^ (k + 1)
      have hcongr : (fun y => U x y * pathIter U μ k y) =ᵐ[μ] fun y => U x y * q ^ k := by
        filter_upwards [ih] with y hy
        rw [hy]
      rw [integral_congr_ae hcongr, integral_mul_const]
      change degree U μ x * q ^ k = _
      rw [hx, pow_succ]
      ring

lemma pathDensity_of_regular (hU : IsGraphon U μ) {q : ℝ}
    (hdeg : ∀ᵐ x ∂μ, degree U μ x = q) (k : ℕ) : pathDensity U μ k = q ^ k := by
  rw [pathDensity, mean, integral_congr_ae (pathIter_ae_eq_of_regular hU hdeg k)]
  simp

/-- Weighted Cauchy–Schwarz: `(∫ U(x,·) f)² ≤ d_U(x) ∫ U(x,·) f²`. -/
lemma sq_kernelOp_le (hU : IsGraphon U μ) (x : Ω) {f : Ω → ℝ} (hf : Good f) :
    (∫ z, U x z * f z ∂μ) ^ 2 ≤ degree U μ x * ∫ z, U x z * (f z * f z) ∂μ := by
  have hI1 : Integrable (fun z => U x z * (f z * f z)) μ := integrable_Uf hU (hf.mul hf) x
  have hI2 : Integrable (fun z => U x z * f z) μ := integrable_Uf hU hf x
  have hI3 : Integrable (fun z => U x z) μ := (goodK_of_isGraphon hU).integrable_row x
  have h : ∀ t : ℝ, 0 ≤ degree U μ x * (t * t) + (2 * ∫ z, U x z * f z ∂μ) * t +
      ∫ z, U x z * (f z * f z) ∂μ := by
    intro t
    have hnn : 0 ≤ ∫ z, U x z * ((f z + t) * (f z + t)) ∂μ :=
      integral_nonneg fun z => mul_nonneg (hU.nonneg x z) (mul_self_nonneg _)
    have e : (fun z => U x z * ((f z + t) * (f z + t))) =
        fun z => U x z * (f z * f z) + (2 * t * (U x z * f z) + t * t * U x z) := by
      funext z; ring
    have hJ2 : Integrable (fun z => 2 * t * (U x z * f z)) μ := hI2.const_mul _
    have hJ3 : Integrable (fun z => t * t * U x z) μ := hI3.const_mul _
    have hJ : Integrable (fun z => 2 * t * (U x z * f z) + t * t * U x z) μ := hJ2.add hJ3
    rw [e, integral_add hI1 hJ, integral_add hJ2 hJ3, integral_const_mul,
      integral_const_mul] at hnn
    have hd : degree U μ x = ∫ z, U x z ∂μ := rfl
    rw [hd]
    nlinarith [hnn]
  have hd := discrim_le_zero h
  unfold discrim at hd
  nlinarith [hd]

lemma integral_comp_row {L : Ω → Ω → ℝ} (hU : IsGraphon U μ) (hL : GoodK L) (x : Ω) :
    ∫ y, comp μ U L x y ∂μ = kernelOp U μ (fun z => ∫ y, L z y ∂μ) x := by
  have hGU := goodK_of_isGraphon hU
  obtain ⟨C, _, hC⟩ := hL.bdd
  have hint : Integrable (Function.uncurry fun y z => U x z * L z y) (μ.prod μ) := by
    have hm : Measurable (Function.uncurry fun y z => U x z * L z y) :=
      (hGU.meas.comp (measurable_const.prodMk measurable_snd)).mul
        (hL.meas.comp (measurable_snd.prodMk measurable_fst))
    refine (integrable_const (1 * C)).mono' hm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (by rw [abs_of_nonneg (hU.nonneg _ _)]; exact hU.le_one _ _) (hC _ _)
      (abs_nonneg _) zero_le_one
  calc ∫ y, comp μ U L x y ∂μ = ∫ y, ∫ z, U x z * L z y ∂μ ∂μ := rfl
    _ = ∫ z, ∫ y, U x z * L z y ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ z, U x z * ∫ y, L z y ∂μ ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        exact integral_const_mul _ _
    _ = kernelOp U μ (fun z => ∫ y, L z y ∂μ) x := rfl

lemma good_rowIntegral {L : Ω → Ω → ℝ} (hL : GoodK L) : Good (fun z => ∫ y, L z y ∂μ) := by
  obtain ⟨C, hC0, hC⟩ := hL.bdd
  refine ⟨(show StronglyMeasurable (Function.uncurry L) from
    hL.meas.stronglyMeasurable).integral_prod_right', ⟨C, hC0, fun z => ?_⟩⟩
  calc |∫ y, L z y ∂μ| ≤ ∫ y, |L z y| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ _y, C ∂μ := integral_mono (hL.integrable_row z).abs (integrable_const C)
        fun y => hC z y
    _ = C := by simp

lemma goodK_sq {K : Ω → Ω → ℝ} (hK : GoodK K) : GoodK (fun x y => K x y * K x y) := by
  obtain ⟨C, hC0, hC⟩ := hK.bdd
  refine ⟨hK.meas.mul hK.meas, ⟨C * C, mul_nonneg hC0 hC0, fun x y => ?_⟩⟩
  rw [abs_mul]
  exact mul_le_mul (hC x y) (hC x y) (abs_nonneg _) hC0

/-- The Hilbert–Schmidt form of the operator-norm bound `‖T_U‖ ≤ q` for a.e. `q`-regular `U`. -/
lemma hsInner_comp_le (hU : IsGraphon U μ) {q : ℝ} (hdeg : ∀ᵐ x ∂μ, degree U μ x = q)
    {K : Ω → Ω → ℝ} (hK : GoodK K) :
    hsInner μ (comp μ U K) (comp μ U K) ≤ q ^ 2 * hsInner μ K K := by
  have hGU := goodK_of_isGraphon hU
  have hUK := goodK_comp (μ := μ) hGU hK
  have hK2 := goodK_sq hK
  have hUK2 := goodK_comp (μ := μ) hGU hK2
  have hD : GoodK (fun x y => degree U μ x * comp μ U (fun x y => K x y * K x y) x y) := by
    obtain ⟨C, hC0, hC⟩ := hUK2.bdd
    obtain ⟨Cd, hCd0, hCd⟩ := (good_degree hU).bdd
    refine ⟨((good_degree hU).meas.measurable.comp measurable_fst).mul hUK2.meas,
      ⟨Cd * C, mul_nonneg hCd0 hC0, fun x y => ?_⟩⟩
    rw [abs_mul]
    exact mul_le_mul (hCd x) (hC x y) (abs_nonneg _) hCd0
  have hint1 := hUK.integrable_mul (μ := μ) hUK
  have hint2 : Integrable (fun p : Ω × Ω =>
      degree U μ p.1 * comp μ U (fun x y => K x y * K x y) p.1 p.2) (μ.prod μ) := by
    have := hD.integrable_mul (μ := μ) goodK_onesKernel
    simpa [onesKernel] using this
  have hrow : ∀ x, ∫ y, comp μ U K x y * comp μ U K x y ∂μ ≤
      ∫ y, degree U μ x * comp μ U (fun x y => K x y * K x y) x y ∂μ := by
    intro x
    refine integral_mono ((goodK_sq hUK).integrable_row x) (hD.integrable_row x) fun y => ?_
    have hf : Good (fun z => K z y) := by
      obtain ⟨C, hC0, hC⟩ := hK.bdd
      exact ⟨(hK.meas.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable,
        ⟨C, hC0, fun z => hC z y⟩⟩
    calc comp μ U K x y * comp μ U K x y = (∫ z, U x z * K z y ∂μ) ^ 2 := by
          simp only [comp]; ring
      _ ≤ _ := sq_kernelOp_le hU x hf
  have h1 : hsInner μ (comp μ U K) (comp μ U K) ≤
      ∫ x, ∫ y, degree U μ x * comp μ U (fun x y => K x y * K x y) x y ∂μ ∂μ := by
    unfold hsInner
    rw [integral_prod _ hint1]
    exact integral_mono hint1.integral_prod_left hint2.integral_prod_left hrow
  set ρ : Ω → ℝ := fun z => ∫ y, K z y * K z y ∂μ with hρdef
  have hρ : Good ρ := good_rowIntegral (μ := μ) hK2
  have h2 : ∫ x, ∫ y, degree U μ x * comp μ U (fun x y => K x y * K x y) x y ∂μ ∂μ =
      q ^ 2 * hsInner μ K K := by
    calc ∫ x, ∫ y, degree U μ x * comp μ U (fun x y => K x y * K x y) x y ∂μ ∂μ
        = ∫ x, degree U μ x * kernelOp U μ ρ x ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          dsimp only
          rw [integral_const_mul, integral_comp_row hU hK2 x]
      _ = ∫ x, q * kernelOp U μ ρ x ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [hdeg] with x hx
          rw [hx]
      _ = q * ∫ x, ρ x * degree U μ x ∂μ := by
          rw [integral_const_mul]
          congr 1
          have hs := kernelOp_symm hU hρ good_one
          rw [kernelOp_one hU] at hs
          simpa only [mul_one] using hs
      _ = q * ∫ x, ρ x * q ∂μ := by
          congr 1
          refine integral_congr_ae ?_
          filter_upwards [hdeg] with x hx
          rw [hx]
      _ = q ^ 2 * hsInner μ K K := by
          rw [integral_mul_const]
          unfold hsInner
          rw [integral_prod _ (hK.integrable_mul hK)]
          ring
  linarith

end OddCycleBound.Equality
