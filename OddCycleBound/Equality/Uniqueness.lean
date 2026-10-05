import OddCycleBound.Equality.Cliques
import OddCycleBound.DenseRegion.Diagonal.Regularity

/-!
# Uniqueness of the extremal graphon (Proposition 6.2 and Corollary 1.2)

"Unique up to graphon equivalence" is formalised as: `W` is, almost everywhere, the pullback of
`completePartite k` along a measurable measure-preserving map `φ : Ω → Fin k`.
Conversely, edge and cycle densities are invariant under such pullbacks.
-/

open MeasureTheory

namespace OddCycleBound

open Equality

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}

/-! ### Densities are invariant under measure-preserving pullback -/

section Pullback

variable {k : ℕ} {φ : Ω → Fin k}

omit [IsProbabilityMeasure μ] in
lemma compPow_pullback (hφ : Measurable φ) (hmap : Measure.map φ μ = uniformFin k) :
    ∀ n x y, compPow μ (fun x y => completePartite k (φ x) (φ y)) n x y =
      compPow (uniformFin k) (completePartite k) n (φ x) (φ y)
  | 0, _, _ => rfl
  | n + 1, x, y => by
      show ∫ z, completePartite k (φ x) (φ z) *
          compPow μ (fun x y => completePartite k (φ x) (φ y)) n z y ∂μ =
        ∫ i, completePartite k (φ x) i * compPow (uniformFin k) (completePartite k) n i (φ y)
          ∂(uniformFin k)
      simp only [compPow_pullback hφ hmap n]
      rw [← hmap, integral_map hφ.aemeasurable
        (measurable_of_finite _).aestronglyMeasurable]

omit [IsProbabilityMeasure μ] in
lemma isGraphon_pullback (hφ : Measurable φ) :
    IsGraphon (fun x y => completePartite k (φ x) (φ y)) μ where
  meas := (measurable_of_finite (Function.uncurry (completePartite k))).comp
    ((hφ.comp measurable_fst).prodMk (hφ.comp measurable_snd))
  nonneg _ _ := (isGraphon_completePartite k).nonneg _ _
  le_one _ _ := (isGraphon_completePartite k).le_one _ _
  symm _ _ := (isGraphon_completePartite k).symm _ _

omit [IsProbabilityMeasure μ] in
lemma cycleDensity_pullback_exact (hφ : Measurable φ)
    (hmap : Measure.map φ μ = uniformFin k) (m : ℕ) :
    cycleDensity μ (fun x y => completePartite k (φ x) (φ y)) m =
      cycleDensity (uniformFin k) (completePartite k) m := by
  rw [cycleDensity, cycleDensity, trace, trace]
  simp only [compPow_pullback hφ hmap]
  rw [← hmap, integral_map hφ.aemeasurable (measurable_of_finite _).aestronglyMeasurable]

omit [IsProbabilityMeasure μ] in
lemma edgeDensity_pullback_exact (hφ : Measurable φ)
    (hmap : Measure.map φ μ = uniformFin k) :
    edgeDensity (fun x y => completePartite k (φ x) (φ y)) μ =
      edgeDensity (completePartite k) (uniformFin k) := by
  have h : ∀ x, degree (fun x y => completePartite k (φ x) (φ y)) μ x =
      degree (completePartite k) (uniformFin k) (φ x) := fun x => by
    rw [degree, degree, ← hmap,
      integral_map hφ.aemeasurable (measurable_of_finite _).aestronglyMeasurable]
  rw [edgeDensity, edgeDensity, mean, mean]
  simp only [h]
  rw [← hmap, integral_map hφ.aemeasurable (measurable_of_finite _).aestronglyMeasurable]

/-- Kernel powers of a.e. equal graphons agree a.e. -/
lemma compPow_ae_eq {W W' : Ω → Ω → ℝ} (hW : IsGraphon W μ) (hW' : IsGraphon W' μ)
    (h : ∀ᵐ p ∂(μ.prod μ), W p.1 p.2 = W' p.1 p.2) :
    ∀ n, ∀ᵐ p ∂(μ.prod μ), compPow μ W n p.1 p.2 = compPow μ W' n p.1 p.2
  | 0 => h
  | n + 1 => by
      have hG := goodK_of_isGraphon hW
      have hG' := goodK_of_isGraphon hW'
      have ih := compPow_ae_eq hW hW' h n
      have hset : MeasurableSet
          {p : Ω × Ω | compPow μ W (n + 1) p.1 p.2 = compPow μ W' (n + 1) p.1 p.2} :=
        measurableSet_eq_fun (goodK_compPow hG (n + 1)).meas (goodK_compPow hG' (n + 1)).meas
      rw [Measure.ae_prod_iff_ae_ae hset]
      filter_upwards [Measure.ae_ae_of_ae_prod h] with x hx
      filter_upwards [Measure.ae_ae_of_ae_prod ih] with y hy
      show ∫ z, W x z * compPow μ W n z y ∂μ = ∫ z, W' x z * compPow μ W' n z y ∂μ
      refine integral_congr_ae ?_
      filter_upwards [hx, hy] with z hz1 hz2
      rw [hz1, compPow_symm hG hW.symm n z y, compPow_symm hG' hW'.symm n z y]
      exact congrArg _ hz2

omit [IsProbabilityMeasure μ] in
lemma hsInner_congr_ae {A A' B B' : Ω → Ω → ℝ}
    (hA : ∀ᵐ p ∂(μ.prod μ), A p.1 p.2 = A' p.1 p.2)
    (hB : ∀ᵐ p ∂(μ.prod μ), B p.1 p.2 = B' p.1 p.2) :
    hsInner μ A B = hsInner μ A' B' := by
  unfold hsInner
  refine integral_congr_ae ?_
  filter_upwards [hA, hB] with p h1 h2
  rw [h1, h2]

/-- Cycle densities (`m ≥ 2`) of a.e. equal graphons agree. -/
lemma cycleDensity_congr_ae {W W' : Ω → Ω → ℝ} (hW : IsGraphon W μ) (hW' : IsGraphon W' μ)
    (h : ∀ᵐ p ∂(μ.prod μ), W p.1 p.2 = W' p.1 p.2) {m : ℕ} (hm : 2 ≤ m) :
    cycleDensity μ W m = cycleDensity μ W' m := by
  have hG := goodK_of_isGraphon hW
  have hG' := goodK_of_isGraphon hW'
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  rw [cycleDensity, cycleDensity, show n + 2 - 1 = n + 1 by omega,
    show compPow μ W (n + 1) = comp μ W (compPow μ W n) from rfl,
    show compPow μ W' (n + 1) = comp μ W' (compPow μ W' n) from rfl,
    trace_comp_eq_hsInner hG (goodK_compPow hG n) (compPow_symm hG hW.symm n),
    trace_comp_eq_hsInner hG' (goodK_compPow hG' n) (compPow_symm hG' hW'.symm n)]
  exact hsInner_congr_ae h (compPow_ae_eq hW hW' h n)

lemma edgeDensity_congr_ae {W W' : Ω → Ω → ℝ} (hW : IsGraphon W μ) (hW' : IsGraphon W' μ)
    (h : ∀ᵐ p ∂(μ.prod μ), W p.1 p.2 = W' p.1 p.2) :
    edgeDensity W μ = edgeDensity W' μ := by
  rw [← integral_prod_eq_edgeDensity hW, ← integral_prod_eq_edgeDensity hW']
  exact integral_congr_ae h

/-- Cycle densities are invariant under measure-preserving pullback: if `W` is a.e. the pullback
of `W_k` along `φ`, then `t(C_m, W) = t(C_m, W_k)` for `m ≥ 2`. (For `m ≤ 1` the formal
`cycleDensity` is the integral over the diagonal of `W`, which is not invariant under changes
on a null set of `Ω × Ω`.) -/
theorem cycleDensity_pullback (hWg : IsGraphon W μ) (φ : Ω → Fin k) (hφ : Measurable φ)
    (hmap : Measure.map φ μ = uniformFin k)
    (hW : ∀ᵐ p ∂(μ.prod μ), W p.1 p.2 = completePartite k (φ p.1) (φ p.2))
    {m : ℕ} (hm : 2 ≤ m) :
    cycleDensity μ W m = cycleDensity (uniformFin k) (completePartite k) m := by
  rw [cycleDensity_congr_ae hWg (isGraphon_pullback hφ) hW hm,
    cycleDensity_pullback_exact hφ hmap]

theorem edgeDensity_pullback (hWg : IsGraphon W μ) (φ : Ω → Fin k) (hφ : Measurable φ)
    (hmap : Measure.map φ μ = uniformFin k)
    (hW : ∀ᵐ p ∂(μ.prod μ), W p.1 p.2 = completePartite k (φ p.1) (φ p.2)) :
    edgeDensity W μ = edgeDensity (completePartite k) (uniformFin k) := by
  rw [edgeDensity_congr_ae hWg (isGraphon_pullback hφ) hW, edgeDensity_pullback_exact hφ hmap]

end Pullback

/-! ### Equality in Theorem 1.1 -/

/-- Equality in Theorem 1.1 forces equality in Theorem 1.3 and `t(C_m, U) = t(P_{m-1}, U)`
(equation `eq:one-colour-gap`). -/
lemma gaps_eq_zero_of_eq (hW : IsGraphon W μ) (hp : 2 / 3 ≤ edgeDensity W μ) {m : ℕ}
    (hm : Odd m) (hm3 : 3 ≤ m)
    (heq : cycleDensity μ W m =
      edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1)) :
    DenseRegion.commonalityGap W μ m = 0 ∧
      cycleDensity μ (compl W) m = pathDensity (compl W) μ (m - 1) := by
  have hgap := DenseRegion.commonality_gap_ge_degree_variance hW hp hm hm3
  have hV : 0 ≤ ((m : ℝ) - 1) *
      (∫ x, (degree W μ x - edgeDensity W μ) ^ 2 ∂μ) ^ ((m - 1) / 2) := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    exact mul_nonneg (by linarith) (pow_nonneg (integral_nonneg fun _ => sq_nonneg _) _)
  have hdel := edge_deletion_general (isGraphon_compl hW) (m - 2)
  rw [show m - 2 + 2 = m by omega, show m - 2 + 1 = m - 1 by omega] at hdel
  have hdef : DenseRegion.commonalityGap W μ m =
      cycleDensity μ W m + cycleDensity μ (compl W) m - pathDensity (compl W) μ (m - 1) -
        (edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1)) := rfl
  constructor <;> linarith

/-- **Proposition 6.2 (forward implication) and the uniqueness in Corollary 1.2.**
If a graphon of edge density `2/3 ≤ p < 1` attains equality in Theorem 1.1, then `p = 1 - 1/k`
for an integer `k ≥ 3`, and `W` is a.e. the pullback of the balanced complete `k`-partite graphon
along a measurable measure-preserving map `φ : Ω → Fin k`. -/
theorem completePartite_unique {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) (hW : IsGraphon W μ)
    (hp : 2 / 3 ≤ edgeDensity W μ) (hp1 : edgeDensity W μ < 1)
    (heq : cycleDensity μ W m =
      edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1)) :
    ∃ k : ℕ, 3 ≤ k ∧ edgeDensity W μ = 1 - 1 / k ∧
      ∃ φ : Ω → Fin k, Measurable φ ∧ Measure.map φ μ = uniformFin k ∧
        ∀ᵐ p ∂(μ.prod μ), W p.1 p.2 = completePartite k (φ p.1) (φ p.2) := by
  set q := 1 - edgeDensity W μ with hqdef
  have hq : 0 < q := by linarith
  have hU := isGraphon_compl hW
  obtain ⟨hgap, hcyc⟩ := gaps_eq_zero_of_eq hW hp hm hm3 heq
  -- `W` is a.e. `p`-regular, so `U = 1 - W` is a.e. `q`-regular
  have hregW := (DenseRegion.commonality_eq_iff_regular hW hp hm hm3).mp hgap
  have hdegU : ∀ᵐ x ∂μ, degree (compl W) μ x = q := by
    filter_upwards [hregW] with x hx
    rw [DenseRegion.degree_compl hW, hx]
  have hcycU : cycleDensity μ (compl W) m = q ^ (m - 1) := by
    rw [hcyc, pathDensity_of_regular hU hdegU]
  obtain ⟨h01, hsq⟩ := regular_cycle_equality hU hq hdegU hm hm3 hcycU
  obtain ⟨k, hkq, φ, hφ, hmap, hφU⟩ := exists_clique_partition hU hq hdegU h01 hsq
  have hk0 : (k : ℝ) ≠ 0 := by
    rintro h; rw [h, zero_mul] at hkq; exact zero_ne_one hkq
  have hqk : q = 1 / k := by field_simp; linarith
  have hpk : edgeDensity W μ = 1 - 1 / k := by linarith
  refine ⟨k, ?_, hpk, φ, hφ, hmap, ?_⟩
  · have h3 : (3 : ℝ) ≤ k := by
      have hkpos : (0 : ℝ) < k := by
        rcases lt_or_gt_of_ne hk0 with h | h
        · exact absurd h (not_lt.mpr (Nat.cast_nonneg k))
        · exact h
      rw [hqk] at hq
      have : 1 / (k : ℝ) ≤ 1 / 3 := by linarith
      rw [div_le_div_iff₀ hkpos (by norm_num)] at this
      linarith
    exact_mod_cast h3
  · filter_upwards [hφU] with p hp
    have : W p.1 p.2 = 1 - compl W p.1 p.2 := by simp [compl]
    rw [this, hp]
    unfold completePartite
    split_ifs <;> norm_num

/-- **Proposition 6.2 (backward implication).** Every a.e. pullback of `W_k` with `k ≥ 2` attains
equality in Theorem 1.1 for every odd `m ≥ 3`. -/
theorem pullback_attains_bound (hWg : IsGraphon W μ) {k : ℕ} (hk : 1 ≤ k) (φ : Ω → Fin k)
    (hφ : Measurable φ) (hmap : Measure.map φ μ = uniformFin k)
    (hW : ∀ᵐ p ∂(μ.prod μ), W p.1 p.2 = completePartite k (φ p.1) (φ p.2))
    {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    cycleDensity μ W m =
      edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) := by
  rw [cycleDensity_pullback hWg φ hφ hmap hW (by omega), edgeDensity_pullback hWg φ hφ hmap hW,
    edgeDensity_completePartite (by omega), cycleDensity_completePartite_odd hk hm]

end OddCycleBound
