import OddCycleBound.Equality.SpectralStep
import OddCycleBound.KPartite

/-!
# The clique decomposition in the proof of Proposition 6.2

Let `U` be an a.e. `q`-regular graphon (`q > 0`) that is `{0,1}`-valued a.e. and satisfies
`∫ U(x,z) U(z,y) dz = q U(x,y)` for a.e. `(x,y)` (equation `eq:equal-neighbourhoods`).
Instead of the paper's iterative block construction we use the relation "the neighbourhoods
`N(x)` and `N(y)` agree up to a null set": it is an equivalence relation, `U` is a.e. the
indicator of this relation, almost every class has measure `q`, and a maximal family of
pairwise inequivalent points of this kind indexes the classes. This yields a measurable,
measure-preserving `φ : Ω → Fin k` with `kq = 1` and `U(x,y) = [φ x = φ y]` a.e.
-/

open MeasureTheory
open scoped ENNReal

namespace OddCycleBound.Equality

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {U : Ω → Ω → ℝ}

/-- `x` and `y` have the same neighbourhood up to a null set. -/
def SameNbhd (μ : Measure Ω) (U : Ω → Ω → ℝ) (x y : Ω) : Prop := ∀ᵐ z ∂μ, U x z = U y z

omit [IsProbabilityMeasure μ] in
lemma SameNbhd.symm {x y : Ω} (h : SameNbhd μ U x y) : SameNbhd μ U y x :=
  h.mono fun _ hz => hz.symm

omit [IsProbabilityMeasure μ] in
lemma SameNbhd.trans {x y z : Ω} (h1 : SameNbhd μ U x y) (h2 : SameNbhd μ U y z) :
    SameNbhd μ U x z := by
  filter_upwards [h1, h2] with w hw1 hw2
  rw [hw1, hw2]

lemma measurableSet_sameNbhd (hU : Measurable (Function.uncurry U)) :
    MeasurableSet {p : Ω × Ω | SameNbhd μ U p.1 p.2} := by
  set D : Set ((Ω × Ω) × Ω) := {r | U r.1.1 r.2 ≠ U r.1.2 r.2} with hDdef
  have hD : MeasurableSet D := by
    have h1 : Measurable fun r : (Ω × Ω) × Ω => U r.1.1 r.2 :=
      hU.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have h2 : Measurable fun r : (Ω × Ω) × Ω => U r.1.2 r.2 :=
      hU.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    exact (measurableSet_eq_fun h1 h2).compl
  have hmeas := measurable_measure_prodMk_left (ν := μ) hD
  have hset : {p : Ω × Ω | SameNbhd μ U p.1 p.2} =
      (fun p => μ (Prod.mk p ⁻¹' D)) ⁻¹' {0} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, SameNbhd, ae_iff,
      hDdef]
    rfl
  rw [hset]
  exact hmeas (measurableSet_singleton 0)

/-- The neighbourhood class of `x`. -/
def nbhdClass (μ : Measure Ω) (U : Ω → Ω → ℝ) (x : Ω) : Set Ω := {y | SameNbhd μ U x y}

lemma measurableSet_nbhdClass (hU : Measurable (Function.uncurry U)) (x : Ω) :
    MeasurableSet (nbhdClass μ U x) :=
  measurable_prodMk_left (measurableSet_sameNbhd (μ := μ) hU)

omit [IsProbabilityMeasure μ] in
lemma disjoint_nbhdClass {x y : Ω} (h : ¬ SameNbhd μ U x y) :
    Disjoint (nbhdClass μ U x) (nbhdClass μ U y) := by
  rw [Set.disjoint_left]
  intro z hzx hzy
  exact h (SameNbhd.trans hzx (SameNbhd.symm hzy))

open Classical in
/-- Under the hypotheses of the clique decomposition, `U` is a.e. the indicator of the relation
`SameNbhd`. -/
lemma ae_eq_ite_sameNbhd (hU : IsGraphon U μ) {q : ℝ} (hq : 0 < q)
    (hdeg : ∀ᵐ x ∂μ, degree U μ x = q)
    (h01 : ∀ᵐ p ∂(μ.prod μ), U p.1 p.2 = 0 ∨ U p.1 p.2 = 1)
    (hsq : ∀ᵐ p ∂(μ.prod μ), comp μ U U p.1 p.2 = q * U p.1 p.2) :
    ∀ᵐ p ∂(μ.prod μ), U p.1 p.2 = if SameNbhd μ U p.1 p.2 then 1 else 0 := by
  have hGU := goodK_of_isGraphon hU
  have hrow : ∀ᵐ x ∂μ, (∀ᵐ z ∂μ, U x z = 0 ∨ U x z = 1) ∧ degree U μ x = q := by
    filter_upwards [Measure.ae_ae_of_ae_prod h01, hdeg] with x hx1 hx2 using ⟨hx1, hx2⟩
  have hfst := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hrow
  have hsnd := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hrow
  filter_upwards [h01, hsq, hfst, hsnd] with p h1 h2 h3 h4
  obtain ⟨x, y⟩ := p
  simp only at h1 h2 h3 h4 ⊢
  have hsq_row : ∀ w, (∀ᵐ z ∂μ, U w z = 0 ∨ U w z = 1) → degree U μ w = q →
      ∫ z, U w z * U w z ∂μ = q := fun w hw hdw => by
    rw [← hdw, degree]
    refine integral_congr_ae (hw.mono fun z hz => ?_)
    rcases hz with h | h <;> simp [h]
  have hxx := hsq_row x h3.1 h3.2
  have hyy := hsq_row y h4.1 h4.2
  have hxy : ∫ z, U x z * U y z ∂μ = q * U x y := by
    rw [← h2]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [hU.symm y z]
  have hIx := hGU.integrable_row (μ := μ) x
  have hIy := hGU.integrable_row (μ := μ) y
  have hmul : ∀ a b : Ω, Integrable (fun z => U a z * U b z) μ := fun a b =>
    integrable_Uf hU ⟨(hGU.meas.comp measurable_prodMk_left).stronglyMeasurable,
      ⟨1, zero_le_one, fun z => by
        show |U b z| ≤ 1
        rw [abs_of_nonneg (hU.nonneg b z)]; exact hU.le_one b z⟩⟩ a
  have hD : ∫ z, (U x z - U y z) ^ 2 ∂μ = 2 * q - 2 * q * U x y := by
    have e : (fun z => (U x z - U y z) ^ 2) =
        fun z => U x z * U x z - 2 * (U x z * U y z) + U y z * U y z := by
      funext z; ring
    have hJ1 : Integrable (fun z => 2 * (U x z * U y z)) μ := (hmul x y).const_mul _
    have hJ : Integrable (fun z => U x z * U x z - 2 * (U x z * U y z)) μ := (hmul x x).sub hJ1
    rw [e, integral_add hJ (hmul y y), integral_sub (hmul x x) hJ1, integral_const_mul, hxx, hyy,
      hxy]
    ring
  have hIsq : Integrable (fun z => (U x z - U y z) ^ 2) μ := by
    have e : (fun z => (U x z - U y z) ^ 2) =
        fun z => U x z * U x z - 2 * (U x z * U y z) + U y z * U y z := by
      funext z; ring
    rw [e]
    have hJ1 : Integrable (fun z => 2 * (U x z * U y z)) μ := (hmul x y).const_mul _
    have hJ : Integrable (fun z => U x z * U x z - 2 * (U x z * U y z)) μ := (hmul x x).sub hJ1
    exact hJ.add (hmul y y)
  rcases h1 with h | h
  · rw [h, if_neg]
    intro hsame
    have h0 : ∫ z, (U x z - U y z) ^ 2 ∂μ = 0 := by
      refine integral_eq_zero_of_ae (hsame.mono fun z hz => ?_)
      simp [hz]
    rw [hD, h] at h0
    linarith
  · rw [h, if_pos]
    have h0 : ∫ z, (U x z - U y z) ^ 2 ∂μ = 0 := by rw [hD, h]; ring
    rw [integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg _) hIsq] at h0
    filter_upwards [h0] with z hz
    have : (U x z - U y z) ^ 2 = 0 := hz
    have := pow_eq_zero_iff two_ne_zero |>.mp this
    linarith

lemma ae_measureReal_nbhdClass (hU : IsGraphon U μ) {q : ℝ} (hq : 0 < q)
    (hdeg : ∀ᵐ x ∂μ, degree U μ x = q)
    (h01 : ∀ᵐ p ∂(μ.prod μ), U p.1 p.2 = 0 ∨ U p.1 p.2 = 1)
    (hsq : ∀ᵐ p ∂(μ.prod μ), comp μ U U p.1 p.2 = q * U p.1 p.2) :
    ∀ᵐ x ∂μ, μ.real (nbhdClass μ U x) = q := by
  have hchar := ae_eq_ite_sameNbhd hU hq hdeg h01 hsq
  filter_upwards [Measure.ae_ae_of_ae_prod hchar, hdeg] with x hx hdx
  rw [← hdx, degree, integral_congr_ae hx,
    ← integral_indicator_one (measurableSet_nbhdClass (μ := μ) hU.meas x)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  by_cases h : SameNbhd μ U x y
  · simp [Set.indicator, nbhdClass, h]
  · simp [Set.indicator, nbhdClass, h]

section Family

variable (μ U) in
/-- A family of `n` pairwise inequivalent points whose classes have measure `q`. -/
def GoodFamily (q : ℝ) (n : ℕ) : Prop :=
  ∃ e : Fin n → Ω, (∀ i, μ.real (nbhdClass μ U (e i)) = q) ∧
    Pairwise fun i j => ¬ SameNbhd μ U (e i) (e j)

lemma measureReal_iUnion_family (hU : Measurable (Function.uncurry U)) {q : ℝ} {n : ℕ}
    {e : Fin n → Ω} (he : ∀ i, μ.real (nbhdClass μ U (e i)) = q)
    (hdist : Pairwise fun i j => ¬ SameNbhd μ U (e i) (e j)) :
    μ.real (⋃ i, nbhdClass μ U (e i)) = n * q := by
  rw [measureReal_iUnion_fintype (fun i j hij => disjoint_nbhdClass (hdist hij))
    (fun i => measurableSet_nbhdClass hU (e i))]
  simp [he]

lemma GoodFamily.card_mul_le (hU : Measurable (Function.uncurry U)) {q : ℝ} {n : ℕ}
    (h : GoodFamily μ U q n) : (n : ℝ) * q ≤ 1 := by
  obtain ⟨e, he, hdist⟩ := h
  rw [← measureReal_iUnion_family hU he hdist]
  exact measureReal_le_one

end Family

/-- **The clique decomposition.** -/
theorem exists_clique_partition (hU : IsGraphon U μ) {q : ℝ} (hq : 0 < q)
    (hdeg : ∀ᵐ x ∂μ, degree U μ x = q)
    (h01 : ∀ᵐ p ∂(μ.prod μ), U p.1 p.2 = 0 ∨ U p.1 p.2 = 1)
    (hsq : ∀ᵐ p ∂(μ.prod μ), comp μ U U p.1 p.2 = q * U p.1 p.2) :
    ∃ k : ℕ, (k : ℝ) * q = 1 ∧ ∃ φ : Ω → Fin k, Measurable φ ∧
      Measure.map φ μ = uniformFin k ∧
      ∀ᵐ p ∂(μ.prod μ), U p.1 p.2 = if φ p.1 = φ p.2 then 1 else 0 := by
  classical
  have hmeas := hU.meas
  -- a maximal good family
  set N := ⌊1 / q⌋₊ with hN
  have hbound : ∀ n, GoodFamily μ U q n → n ≤ N := fun n hn => by
    apply Nat.le_floor
    rw [le_div_iff₀ hq]
    exact hn.card_mul_le hmeas
  set k := Nat.findGreatest (GoodFamily μ U q) N with hk
  have h0 : GoodFamily μ U q 0 := ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  have hkgood : GoodFamily μ U q k := Nat.findGreatest_spec (Nat.zero_le N) h0
  have hknot : ¬ GoodFamily μ U q (k + 1) := by
    intro hk1
    have := hbound _ hk1
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self k) this hk1
  obtain ⟨e, he, hdist⟩ := hkgood
  -- every point whose class has measure `q` is equivalent to some `e i`
  have hcover : ∀ x, μ.real (nbhdClass μ U x) = q → ∃ i, SameNbhd μ U (e i) x := by
    intro x hx
    by_contra hcon
    simp only [not_exists] at hcon
    apply hknot
    refine ⟨Fin.snoc (α := fun _ => Ω) e x, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hx
      · simpa using he j
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
          induction j using Fin.lastCases with
          | last => exact absurd rfl hij
          | cast j =>
              simp only [Fin.snoc_last, Fin.snoc_castSucc]
              exact fun h => hcon j h.symm
      | cast i =>
          induction j using Fin.lastCases with
          | last =>
              simp only [Fin.snoc_last, Fin.snoc_castSucc]
              exact hcon i
          | cast j =>
              simp only [Fin.snoc_castSucc]
              exact hdist fun h => hij (by rw [h])
  have hclass := ae_measureReal_nbhdClass hU hq hdeg h01 hsq
  have hae_cover : ∀ᵐ x ∂μ, ∃ i, x ∈ nbhdClass μ U (e i) := by
    filter_upwards [hclass] with x hx using hcover x hx
  -- the classes of the family cover `Ω` up to a null set
  set C : Set Ω := ⋃ i, nbhdClass μ U (e i) with hC
  have hCmeas : MeasurableSet C := MeasurableSet.iUnion fun i => measurableSet_nbhdClass hmeas _
  have hCcompl : μ Cᶜ = 0 := by
    have hmem : ∀ᵐ x ∂μ, x ∈ C := by
      filter_upwards [hae_cover] with x hx
      simpa [hC] using hx
    exact ae_iff.mp hmem
  have hCreal : μ.real C = 1 := by
    rw [measureReal_def, measure_congr (ae_eq_univ.mpr hCcompl), measure_univ,
      ENNReal.toReal_one]
  have hkq : (k : ℝ) * q = 1 := by
    rw [← hCreal, hC, measureReal_iUnion_family hmeas he hdist]
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hkq; simp at hkq
    · exact h
  -- uniqueness of the index
  have huniq : ∀ x i j, SameNbhd μ U (e i) x → SameNbhd μ U (e j) x → i = j := by
    intro x i j hi hj
    by_contra hij
    exact hdist hij (hi.trans hj.symm)
  -- the labelling map
  let φ : Ω → Fin k := fun x =>
    if h : ∃ i, SameNbhd μ U (e i) x then Classical.choose h else ⟨0, hkpos⟩
  have hφ : ∀ x i, SameNbhd μ U (e i) x → φ x = i := by
    intro x i hi
    have h : ∃ i, SameNbhd μ U (e i) x := ⟨i, hi⟩
    simp only [φ, dif_pos h]
    exact huniq x _ _ (Classical.choose_spec h) hi
  have hpre : ∀ i, φ ⁻¹' {i} =
      nbhdClass μ U (e i) ∪ (Cᶜ ∩ {_x | (⟨0, hkpos⟩ : Fin k) = i}) := by
    intro i
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_inter_iff,
      Set.mem_compl_iff, Set.mem_setOf_eq, hC, Set.mem_iUnion, not_exists]
    constructor
    · intro hx
      by_cases h : ∃ j, SameNbhd μ U (e j) x
      · obtain ⟨j, hj⟩ := h
        left
        rw [hφ x j hj] at hx
        rw [← hx]; exact hj
      · right
        refine ⟨fun j hj => h ⟨j, hj⟩, ?_⟩
        rw [← hx]
        simp only [φ, dif_neg h]
    · rintro (hx | ⟨hx, hi⟩)
      · exact hφ x i hx
      · rw [← hi]
        have hx' : ¬ ∃ j, SameNbhd μ U (e j) x := fun ⟨j, hj⟩ => hx j hj
        simp only [φ, dif_neg hx']
  have hφmeas : Measurable φ := by
    refine measurable_to_countable' fun i => ?_
    rw [hpre i]
    exact (measurableSet_nbhdClass hmeas _).union (hCmeas.compl.inter (MeasurableSet.const _))
  refine ⟨k, hkq, φ, hφmeas, ?_, ?_⟩
  · -- `φ` is measure preserving
    refine Measure.ext_of_singleton fun i => ?_
    rw [Measure.map_apply hφmeas (measurableSet_singleton i), hpre i]
    have hnull : μ (Cᶜ ∩ {_x | (⟨0, hkpos⟩ : Fin k) = i}) = 0 :=
      measure_mono_null Set.inter_subset_left hCcompl
    rw [le_antisymm ((measure_union_le _ _).trans (by rw [hnull, add_zero]))
      (measure_mono Set.subset_union_left)]
    have hq' : μ (nbhdClass μ U (e i)) = ENNReal.ofReal q := by
      rw [← he i, ofReal_measureReal]
    rw [hq', uniformFin, Measure.smul_apply, Measure.count_singleton, smul_eq_mul, mul_one]
    have hqk : q = 1 / k := by
      have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hkpos.ne'
      field_simp; linarith
    rw [hqk, one_div, ENNReal.ofReal_inv_of_pos (by exact_mod_cast hkpos),
      ENNReal.ofReal_natCast]
  · have hchar := ae_eq_ite_sameNbhd hU hq hdeg h01 hsq
    have hfst := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hae_cover
    have hsnd := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hae_cover
    filter_upwards [hchar, hfst, hsnd] with p hp h1 h2
    obtain ⟨i, hi⟩ := h1
    obtain ⟨j, hj⟩ := h2
    rw [hp, hφ _ i hi, hφ _ j hj]
    have hiff : SameNbhd μ U p.1 p.2 ↔ i = j := by
      constructor
      · intro hs
        exact huniq p.2 i j (hi.trans hs) hj
      · rintro rfl
        exact hi.symm.trans hj
    by_cases hij : i = j
    · rw [if_pos (hiff.mpr hij), if_pos hij]
    · rw [if_neg (fun h => hij (hiff.mp h)), if_neg hij]

end OddCycleBound.Equality
