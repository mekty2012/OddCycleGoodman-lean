import OddCycleBound.Equality.RegularKernel

/-!
# The spectral step of Proposition 7.2, without eigenvalues

Let `U` be an a.e. `q`-regular graphon with `q > 0` and `t(C_m, U) = q^{m-1}` for an odd `m ≥ 3`.
Writing `T n = trace (compPow U n) = t(C_{n+1}, U)`, the Hilbert–Schmidt pairings of kernel
powers are `⟨U^{a+1}, U^{b+1}⟩ = T (a + b + 1)`. The operator bound gives
`T (2j+3) ≤ q² T (2j+1)`, Cauchy–Schwarz gives `T(2a)² ≤ T(2a-1) T(2a+1)`, and `T 1 = ∫∫ U² ≤ q`.
With `m = 2a + 1` this is the chain `q^{m-1} = t(C_m, U) ≤ q^{m-2} ∫∫ U² ≤ q^{m-1}` of the paper.
Its equality cases give `∫∫ U² = ∫∫ U`, hence `U ∈ {0,1}` a.e., and
`‖U ∘ U - q U‖²_HS = 0`, which is `T_U² = q T_U` at the level of kernels.
-/

open MeasureTheory

namespace OddCycleBound.Equality

/-! ### A numerical lemma -/

section Numerical

variable {q : ℝ} (T : ℕ → ℝ)

lemma odd_trace_le (h1 : T 1 ≤ q) (hstep : ∀ j, T (2 * j + 3) ≤ q ^ 2 * T (2 * j + 1)) :
    ∀ j, T (2 * j + 1) ≤ q ^ (2 * j + 1) := by
  intro j
  induction j with
  | zero => simpa using h1
  | succ j ih =>
      have := hstep j
      calc T (2 * (j + 1) + 1) = T (2 * j + 3) := by ring_nf
        _ ≤ q ^ 2 * T (2 * j + 1) := this
        _ ≤ q ^ 2 * q ^ (2 * j + 1) := mul_le_mul_of_nonneg_left ih (by positivity)
        _ = q ^ (2 * (j + 1) + 1) := by ring

lemma odd_trace_down (hstep : ∀ j, T (2 * j + 3) ≤ q ^ 2 * T (2 * j + 1)) :
    ∀ i j, T (2 * (i + j) + 1) ≤ q ^ (2 * i) * T (2 * j + 1) := by
  intro i j
  induction i with
  | zero => simp
  | succ i ih =>
      calc T (2 * (i + 1 + j) + 1) = T (2 * (i + j) + 3) := by ring_nf
        _ ≤ q ^ 2 * T (2 * (i + j) + 1) := hstep _
        _ ≤ q ^ 2 * (q ^ (2 * i) * T (2 * j + 1)) :=
            mul_le_mul_of_nonneg_left ih (by positivity)
        _ = q ^ (2 * (i + 1)) * T (2 * j + 1) := by ring

/-- The equality case of the chain: if `T (2a) = q^{2a}`, then `T (2j+1) = q^{2j+1}` for
every `j ≤ a`. -/
lemma odd_trace_eq (hq : 0 < q) {a : ℕ} (ha : 1 ≤ a) (h1 : T 1 ≤ q)
    (hT0 : ∀ j, 0 ≤ T (2 * j + 1))
    (hstep : ∀ j, T (2 * j + 3) ≤ q ^ 2 * T (2 * j + 1))
    (hcs : T (2 * a) ^ 2 ≤ T (2 * a - 1) * T (2 * a + 1))
    (hTm : T (2 * a) = q ^ (2 * a)) :
    ∀ j ≤ a, T (2 * j + 1) = q ^ (2 * j + 1) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hle := odd_trace_le T h1 hstep
  set Q := q ^ (2 * b + 1) with hQ
  have hQpos : 0 < Q := by positivity
  have hX0 := hT0 b
  have hXle : T (2 * b + 1) ≤ Q := hle b
  have hY : T (2 * b + 3) ≤ q ^ 2 * T (2 * b + 1) := hstep b
  have hcs' : (Q * q) ^ 2 ≤ T (2 * b + 1) * T (2 * b + 3) := by
    have e1 : 2 * (b + 1) - 1 = 2 * b + 1 := by omega
    have e2 : 2 * (b + 1) + 1 = 2 * b + 3 := by omega
    rw [e1, e2, hTm] at hcs
    calc (Q * q) ^ 2 = (q ^ (2 * (b + 1))) ^ 2 := by rw [hQ]; ring
      _ ≤ _ := hcs
  have hq2 : 0 < q ^ 2 := by positivity
  have hX : T (2 * b + 1) = Q := by
    have : Q ^ 2 * q ^ 2 ≤ q ^ 2 * T (2 * b + 1) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hY hX0]
    have hsq : Q ^ 2 ≤ T (2 * b + 1) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (T (2 * b + 1) - Q)]
  have hYeq : T (2 * b + 3) = q ^ 2 * Q := by
    rw [hX] at hcs' hY
    have : Q * (Q * q ^ 2) ≤ Q * T (2 * b + 3) := by nlinarith
    have := le_of_mul_le_mul_left this hQpos
    linarith
  intro j hj
  have hdown := odd_trace_down T hstep (b + 1 - j) j
  rw [show 2 * (b + 1 - j + j) + 1 = 2 * b + 3 by omega, hYeq] at hdown
  have hpos : 0 < q ^ (2 * (b + 1 - j)) := by positivity
  have hlow : q ^ (2 * j + 1) ≤ T (2 * j + 1) := by
    have e : q ^ 2 * Q = q ^ (2 * (b + 1 - j)) * q ^ (2 * j + 1) := by
      rw [hQ, ← pow_add, ← pow_add]; congr 1; omega
    rw [e] at hdown
    exact le_of_mul_le_mul_left hdown hpos
  exact le_antisymm (hle j) hlow

end Numerical

/-! ### The kernel-level statement -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

lemma edgeDensity_of_regular {q : ℝ}
    (hdeg : ∀ᵐ x ∂μ, degree U μ x = q) : edgeDensity U μ = q := by
  rw [edgeDensity, mean, integral_congr_ae hdeg]
  simp

lemma integral_prod_eq_edgeDensity (hU : IsGraphon U μ) :
    ∫ p, U p.1 p.2 ∂(μ.prod μ) = edgeDensity U μ := by
  have hint : Integrable (fun p : Ω × Ω => U p.1 p.2) (μ.prod μ) :=
    (goodK_of_isGraphon hU).integrable_prod
  rw [integral_prod _ hint]
  rfl

lemma hsInner_self_le_edgeDensity (hU : IsGraphon U μ) :
    hsInner μ U U ≤ edgeDensity U μ := by
  have hGU := goodK_of_isGraphon hU
  rw [← integral_prod_eq_edgeDensity hU]
  refine integral_mono (hGU.integrable_mul hGU) hGU.integrable_prod fun p => ?_
  have h0 := hU.nonneg p.1 p.2
  have h1 := hU.le_one p.1 p.2
  show U p.1 p.2 * U p.1 p.2 ≤ U p.1 p.2
  nlinarith

lemma zero_or_one_of_hsInner_self_eq (hU : IsGraphon U μ)
    (h : hsInner μ U U = edgeDensity U μ) :
    ∀ᵐ p ∂(μ.prod μ), U p.1 p.2 = 0 ∨ U p.1 p.2 = 1 := by
  have hGU := goodK_of_isGraphon hU
  rw [← integral_prod_eq_edgeDensity hU, hsInner] at h
  have hI1 : Integrable (fun p : Ω × Ω => U p.1 p.2) (μ.prod μ) := hGU.integrable_prod
  have hI2 : Integrable (fun p : Ω × Ω => U p.1 p.2 * U p.1 p.2) (μ.prod μ) :=
    hGU.integrable_mul hGU
  have hI : Integrable (fun p : Ω × Ω => U p.1 p.2 - U p.1 p.2 * U p.1 p.2) (μ.prod μ) :=
    hI1.sub hI2
  have hdiff : ∫ p, (U p.1 p.2 - U p.1 p.2 * U p.1 p.2) ∂(μ.prod μ) = 0 := by
    rw [integral_sub hI1 hI2]
    linarith
  rw [integral_eq_zero_iff_of_nonneg (fun p => by
      have h0 := hU.nonneg p.1 p.2
      have h1 := hU.le_one p.1 p.2
      show 0 ≤ U p.1 p.2 - U p.1 p.2 * U p.1 p.2
      nlinarith) hI] at hdiff
  filter_upwards [hdiff] with p hp
  have hp' : U p.1 p.2 * (1 - U p.1 p.2) = 0 := by
    have : U p.1 p.2 - U p.1 p.2 * U p.1 p.2 = 0 := hp
    linarith
  rcases mul_eq_zero.mp hp' with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

/-- **The spectral step of Proposition 7.2.** If `U` is an a.e. `q`-regular graphon with `q > 0`
and `t(C_m, U) = q^{m-1}` for an odd `m ≥ 3`, then `U` is `{0,1}`-valued a.e. and
`∫ U(x,z) U(z,y) dz = q U(x,y)` for a.e. `(x,y)`. -/
theorem regular_cycle_equality (hU : IsGraphon U μ) {q : ℝ} (hq : 0 < q)
    (hdeg : ∀ᵐ x ∂μ, degree U μ x = q) {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m)
    (hcyc : cycleDensity μ U m = q ^ (m - 1)) :
    (∀ᵐ p ∂(μ.prod μ), U p.1 p.2 = 0 ∨ U p.1 p.2 = 1) ∧
      ∀ᵐ p ∂(μ.prod μ), comp μ U U p.1 p.2 = q * U p.1 p.2 := by
  have hGU := goodK_of_isGraphon hU
  set T : ℕ → ℝ := fun n => trace μ (compPow μ U n) with hTdef
  have hP : ∀ a b, hsInner μ (compPow μ U a) (compPow μ U b) = T (a + b + 1) :=
    fun a b => hsInner_compPow hU a b
  have hT0 : ∀ j, 0 ≤ T (2 * j + 1) := fun j => by
    rw [show 2 * j + 1 = j + j + 1 by ring, ← hP]
    exact hsInner_self_nonneg _
  have hedge := edgeDensity_of_regular hdeg
  have hT1eq : hsInner μ U U = T 1 := hP 0 0
  have h1 : T 1 ≤ q := by
    have := hsInner_self_le_edgeDensity (μ := μ) hU
    rw [hedge, hT1eq] at this
    exact this
  have hstep : ∀ j, T (2 * j + 3) ≤ q ^ 2 * T (2 * j + 1) := fun j => by
    have h := hsInner_comp_le hU hdeg (goodK_compPow (μ := μ) hGU j)
    rw [show comp μ U (compPow μ U j) = compPow μ U (j + 1) from rfl, hP, hP] at h
    rw [show 2 * j + 3 = j + 1 + (j + 1) + 1 by ring, show 2 * j + 1 = j + j + 1 by ring]
    exact h
  obtain ⟨a, rfl⟩ := hm
  have ha : 1 ≤ a := by omega
  have hTm : T (2 * a) = q ^ (2 * a) := by
    simpa [cycleDensity] using hcyc
  have hcs : T (2 * a) ^ 2 ≤ T (2 * a - 1) * T (2 * a + 1) := by
    have h := hsInner_sq_le (μ := μ) (goodK_compPow (μ := μ) hGU (a - 1)) (goodK_compPow (μ := μ) hGU a)
    rw [hP, hP, hP] at h
    rw [show a - 1 + a + 1 = 2 * a by omega, show a - 1 + (a - 1) + 1 = 2 * a - 1 by omega,
      show a + a + 1 = 2 * a + 1 by omega] at h
    exact h
  have hodd := odd_trace_eq T hq ha h1 hT0 hstep hcs hTm
  have hT1 : T 1 = q := by simpa using hodd 0 (by omega)
  have hT3 : T 3 = q ^ 3 := by simpa using hodd 1 ha
  -- `T 2 = q²`
  have hT2 : T 2 = q ^ 2 := by
    rcases Nat.eq_or_lt_of_le ha with h | h
    · subst h; simpa using hTm
    · have hT5 : T 5 = q ^ 5 := by simpa using hodd 2 (by omega)
      have hY : hsInner μ (fun x y => compPow μ U 2 x y - q ^ 2 * compPow μ U 0 x y)
          (fun x y => compPow μ U 2 x y - q ^ 2 * compPow μ U 0 x y) = 0 := by
        rw [hsInner_sub_smul_self (goodK_compPow (μ := μ) hGU 2) (goodK_compPow (μ := μ) hGU 0), hP, hP, hP]
        norm_num [hT5, hT3, hT1]
        ring
      have hshift : ∀ b, T (b + 3) = q ^ 2 * T (b + 1) := fun b => by
        have h0 := hsInner_eq_zero_of_self_eq_zero (goodK_compPow (μ := μ) hGU b)
          (goodK_sub_smul (goodK_compPow (μ := μ) hGU 2) (goodK_compPow (μ := μ) hGU 0) _) hY
        rw [hsInner_sub_left (goodK_compPow (μ := μ) hGU 2) (goodK_compPow (μ := μ) hGU 0)
          (goodK_compPow (μ := μ) hGU b), hP, hP] at h0
        rw [show b + 3 = b + 2 + 1 by ring, show b + 1 = b + 0 + 1 by ring]
        linarith
      have hev : ∀ i, T (2 * i + 2) = q ^ (2 * i) * T 2 := fun i => by
        induction i with
        | zero => simp
        | succ i ih =>
            rw [show 2 * (i + 1) + 2 = (2 * i + 1) + 3 by ring, hshift,
              show 2 * i + 1 + 1 = 2 * i + 2 by ring, ih]
            ring
      have h2a := hev (a - 1)
      rw [show 2 * (a - 1) + 2 = 2 * a by omega, hTm] at h2a
      have hpos : 0 < q ^ (2 * (a - 1)) := by positivity
      have e : q ^ (2 * a) = q ^ (2 * (a - 1)) * q ^ 2 := by
        rw [← pow_add]; congr 1; omega
      rw [e] at h2a
      exact (mul_left_cancel₀ hpos.ne' h2a).symm
  refine ⟨zero_or_one_of_hsInner_self_eq hU ?_, ?_⟩
  · rw [hedge, hT1eq, hT1]
  · have hZ : hsInner μ (fun x y => compPow μ U 1 x y - q * compPow μ U 0 x y)
        (fun x y => compPow μ U 1 x y - q * compPow μ U 0 x y) = 0 := by
      rw [hsInner_sub_smul_self (goodK_compPow (μ := μ) hGU 1) (goodK_compPow (μ := μ) hGU 0), hP, hP, hP]
      norm_num [hT3, hT2, hT1]
      ring
    filter_upwards [ae_eq_zero_of_hsInner_self_eq_zero
      (goodK_sub_smul (goodK_compPow (μ := μ) hGU 1) (goodK_compPow (μ := μ) hGU 0) _) hZ] with p hp
    have : compPow μ U 1 p.1 p.2 - q * compPow μ U 0 p.1 p.2 = 0 := hp
    change compPow μ U 1 p.1 p.2 = q * compPow μ U 0 p.1 p.2
    linarith

end OddCycleBound.Equality
