import OddCycleBound.DenseRegion.Diagonal.Commonality

/-!
# Degree variance and equality in strengthened extended commonality (Proposition 6.1)

`Ψ_m(W)` is the gap in Theorem 1.3. Through the excursion expansion it equals
`momentPhi m q (specMoment U μ)`, whose top excursion term (`r = (m-1)/2`) is
`(m - 1) · (s 0)^((m-1)/2)` with `s 0 = ∫ (d_W - p)²`, while every other term is nonnegative.
-/

open MeasureTheory
open scoped BigOperators

namespace OddCycleBound.DenseRegion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {W : Ω → Ω → ℝ}

/-- The gap `Ψ_m(W)` between the two sides of Theorem 1.3. -/
noncomputable def commonalityGap (W : Ω → Ω → ℝ) (μ : Measure Ω) (m : ℕ) : ℝ :=
  cycleDensity μ W m + cycleDensity μ (compl W) m - pathDensity (compl W) μ (m - 1)
    - (edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1))

theorem commonalityGap_eq_momentPhi (hW : IsGraphon W μ) {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    commonalityGap W μ m = momentPhi m (1 - edgeDensity W μ) (specMoment (compl W) μ) := by
  have h1 := cycleDensity_eq_neckSum_add hW hm hm3
  have h2 := neckSum_eq_baseline_add_momentPhi hW hm hm3
  unfold commonalityGap
  linarith

lemma momentConv_zero_right (s : ℕ → ℝ) : ∀ r, momentConv s r 0 = s 0 ^ r
  | 0 => rfl
  | r + 1 => by
      rw [momentConv_succ, Finset.sum_range_one, Nat.sub_self, momentConv_zero_right s r,
        pow_succ]
      ring

/-- The top excursion term: for `m = 2r + 1`, `P_{m,r}` is the constant `m - 1`. -/
lemma momentPhiTerm_top {r : ℕ} (hr : 1 ≤ r) (q : ℝ) (s : ℕ → ℝ) :
    momentPhiTerm (2 * r + 1) r q s = (2 * r : ℝ) * s 0 ^ r := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  unfold momentPhiTerm momentShiftTerm momentPathTerm
  have h1 : 2 * (r + 1) + 1 - 2 * (r + 1) = 1 := by omega
  simp only [h1, Finset.sum_range_succ, Finset.sum_range_zero, Nat.add_sub_cancel, zero_add,
    Nat.sub_zero, Nat.sub_self, pow_zero, pow_one, momentConv_zero_right,
    Nat.choose_self, Nat.lt_irrefl, if_false, zero_lt_one, if_true]
  rw [show 1 + r = r + 1 by omega, Nat.choose_succ_self_right]
  push_cast
  field_simp
  ring

lemma momentPhiTerm_congr_of_le {m r : ℕ} (q : ℝ) {s t : ℕ → ℝ}
    (h : ∀ j ≤ m, s j = t j) : momentPhiTerm m r q s = momentPhiTerm m r q t := by
  unfold momentPhiTerm momentShiftTerm momentPathTerm
  congr 1 <;> refine Finset.sum_congr rfl fun j hj => ?_
  all_goals
    rw [momentConv_congr_of_le _ _ fun ell hell => h ell (by
      have hjlt : j < m - 2 * r + 1 := Finset.mem_range.mp hj
      omega)]

/-- Every excursion term of `Ψ_m` is nonnegative for `p ≥ 2/3`. -/
lemma momentPhiTerm_specMoment_nonneg (hW : IsGraphon W μ) (hp : 2 / 3 ≤ edgeDensity W μ)
    {m r : ℕ} (hm : Odd m) (hr : 1 ≤ r) (h2r : 2 * r < m) :
    0 ≤ momentPhiTerm m r (1 - edgeDensity W μ) (specMoment (compl W) μ) := by
  have hU := isGraphon_compl hW
  rw [momentPhiTerm_congr_of_le (t := atomicMoment (graphonAtomWeight hU m)
      (graphonAtomEigenvalue hU m)) _ fun j hj => specMoment_eq_graphonAtomicMoment hU hj,
    momentPhiTerm_eq_momentKernelTerm]
  exact momentKernelTerm_nonneg_of_atomic (by omega) (by omega) _ _ _
    (graphonAtomWeight_nonneg hU m) (graphonAtomEigenvalue_mem_halfInterval hU m)
    fun ell hell => diagKernel_nonneg_uniform diagKernelPosEll_unconditional hm hr h2r
      (by linarith [edgeDensity_le_one hW]) (by linarith) hell

lemma specMoment_compl_zero (hW : IsGraphon W μ) :
    specMoment (compl W) μ 0 = ∫ x, (degree W μ x - edgeDensity W μ) ^ 2 ∂μ := by
  show ∫ x, degCentered (compl W) μ x * degCentered (compl W) μ x ∂μ = _
  rw [degCentered_compl hW]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [degCentered]
  ring

lemma momentPhi_ge_top (hW : IsGraphon W μ) (hp : 2 / 3 ≤ edgeDensity W μ) {m : ℕ}
    (hm : Odd m) (hm3 : 3 ≤ m) :
    (m - 1 : ℝ) * specMoment (compl W) μ 0 ^ ((m - 1) / 2) ≤
      momentPhi m (1 - edgeDensity W μ) (specMoment (compl W) μ) := by
  obtain ⟨t, rfl⟩ := hm
  have ht : (2 * t + 1 - 1) / 2 = (t - 1) + 1 := by omega
  unfold momentPhi
  rw [ht, Finset.sum_range_succ, show t - 1 + 1 = t by omega,
    momentPhiTerm_top (by omega)]
  have hrest : 0 ≤ ∑ k ∈ Finset.range (t - 1),
      momentPhiTerm (2 * t + 1) (k + 1) (1 - edgeDensity W μ) (specMoment (compl W) μ) :=
    Finset.sum_nonneg fun k hk => by
      have := Finset.mem_range.mp hk
      exact momentPhiTerm_specMoment_nonneg hW hp ⟨t, rfl⟩ (by omega) (by omega)
  push_cast
  linarith

/-- **Proposition 6.1**, equation `eq:degree-variance-gap`:
`Ψ_m(W) ≥ (m - 1) (∫ (d_W - p)²)^((m-1)/2)` for `p ≥ 2/3`. -/
theorem commonality_gap_ge_degree_variance (hW : IsGraphon W μ)
    (hp : 2 / 3 ≤ edgeDensity W μ) {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    (m - 1 : ℝ) * (∫ x, (degree W μ x - edgeDensity W μ) ^ 2 ∂μ) ^ ((m - 1) / 2) ≤
      commonalityGap W μ m := by
  rw [commonalityGap_eq_momentPhi hW hm hm3, ← specMoment_compl_zero hW]
  exact momentPhi_ge_top hW hp hm hm3

lemma specMoment_compl_eq_zero_of_regular (hW : IsGraphon W μ)
    (hreg : ∀ᵐ x ∂μ, degree W μ x = edgeDensity W μ) :
    specMoment (compl W) μ = fun _ => 0 := by
  funext j
  show ∫ x, degCentered (compl W) μ x * compressIter (compl W) μ j x ∂μ = 0
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hreg] with x hx
  rw [degCentered_compl hW]
  simp [degCentered, hx]

lemma momentPhi_zero_seq (m : ℕ) (q : ℝ) : momentPhi m q (fun _ => 0) = 0 := by
  unfold momentPhi momentPhiTerm momentShiftTerm momentPathTerm
  refine Finset.sum_eq_zero fun k _ => ?_
  simp [momentConv_succ]

/-- The backward implication of Proposition 6.1 holds at every edge density: a `p`-regular
graphon attains equality in Theorem 1.3. -/
theorem commonalityGap_eq_zero_of_regular (hW : IsGraphon W μ) {m : ℕ} (hm : Odd m)
    (hm3 : 3 ≤ m) (hreg : ∀ᵐ x ∂μ, degree W μ x = edgeDensity W μ) :
    commonalityGap W μ m = 0 := by
  rw [commonalityGap_eq_momentPhi hW hm hm3, specMoment_compl_eq_zero_of_regular hW hreg,
    momentPhi_zero_seq]

/-- **Proposition 6.1**: for `p ≥ 2/3`, `Ψ_m(W) = 0` if and only if `W` is a.e. `p`-regular. -/
theorem commonality_eq_iff_regular (hW : IsGraphon W μ) (hp : 2 / 3 ≤ edgeDensity W μ)
    {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    commonalityGap W μ m = 0 ↔ ∀ᵐ x ∂μ, degree W μ x = edgeDensity W μ := by
  refine ⟨fun h0 => ?_, commonalityGap_eq_zero_of_regular hW hm hm3⟩
  have hb := commonality_gap_ge_degree_variance hW hp hm hm3
  rw [h0] at hb
  set V := ∫ x, (degree W μ x - edgeDensity W μ) ^ 2 ∂μ with hVdef
  have hV0 : 0 ≤ V := integral_nonneg fun x => sq_nonneg _
  have hm1 : (0 : ℝ) < m - 1 := by
    have : (3 : ℝ) ≤ m := by exact_mod_cast hm3
    linarith
  have hpow : V ^ ((m - 1) / 2) ≤ 0 := by
    by_contra hcon
    have := mul_pos hm1 (not_le.mp hcon)
    linarith
  have hVz : V = 0 := by
    have hpos : 0 ≤ V ^ ((m - 1) / 2) := pow_nonneg hV0 _
    exact pow_eq_zero_iff (n := (m - 1) / 2) (by omega) |>.mp (le_antisymm hpow hpos)
  have hint : Integrable (fun x => (degree W μ x - edgeDensity W μ) ^ 2) μ := by
    refine ((good_degCentered hW).mul (good_degCentered hW)).integrable.congr
      (ae_of_all _ fun x => ?_)
    simp only [degCentered]; ring
  rw [hVdef, integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) hint] at hVz
  filter_upwards [hVz] with x hx
  have : (degree W μ x - edgeDensity W μ) ^ 2 = 0 := hx
  nlinarith [sq_nonneg (degree W μ x - edgeDensity W μ)]

end OddCycleBound.DenseRegion
