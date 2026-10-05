import OddCycleBound.DenseRegion.Diagonal.DenseRegionEndgame
import OddCycleBound.BasicBounds

/-!
# The balanced complete `k`-partite graphon (Corollary 1.2, minimality)

The balanced complete `k`-partite graphon `W_k` is modelled on the finite probability space
`Fin k` with the uniform measure: `completePartite k i j = 1` if `i ≠ j` and `0` otherwise.
(The graphon `W_k` on `[0,1]` of the paper is its pullback along `x ↦ ⌈kx⌉`.)
We compute its kernel powers and cycle densities (equation `eq:intro-kpartite-value`), and deduce
from Theorem 1.1 that it minimises the `C_m`-density at edge density `1 - 1/k`.
-/

open MeasureTheory
open scoped ENNReal

namespace OddCycleBound

/-- The balanced complete `k`-partite graphon on the vertex set `Fin k`. -/
def completePartite (k : ℕ) : Fin k → Fin k → ℝ := fun i j => if i = j then 0 else 1

/-- The uniform probability measure on `Fin k`. -/
noncomputable def uniformFin (k : ℕ) : Measure (Fin k) := (k : ℝ≥0∞)⁻¹ • Measure.count

lemma uniformFin_univ {k : ℕ} (hk : k ≠ 0) : uniformFin k Set.univ = 1 := by
  rw [uniformFin, Measure.smul_apply, ← Finset.coe_univ, Measure.count_apply_finset,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hk) (ENNReal.natCast_ne_top k)

instance (k : ℕ) : IsFiniteMeasure (uniformFin k) := by
  refine ⟨?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have : (Set.univ : Set (Fin 0)) = ∅ := Set.eq_empty_of_isEmpty _
    simp [uniformFin, this]
  · rw [uniformFin_univ hk.ne']; exact ENNReal.one_lt_top

lemma integral_uniformFin (k : ℕ) (f : Fin k → ℝ) :
    ∫ x, f x ∂(uniformFin k) = (1 / k : ℝ) * ∑ x, f x := by
  rw [integral_fintype Integrable.of_finite, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [measureReal_def, uniformFin, Measure.smul_apply, Measure.count_singleton,
    smul_eq_mul, mul_one, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]

lemma isGraphon_completePartite (k : ℕ) : IsGraphon (completePartite k) (uniformFin k) where
  meas := measurable_of_finite _
  nonneg i j := by unfold completePartite; split_ifs <;> norm_num
  le_one i j := by unfold completePartite; split_ifs <;> norm_num
  symm i j := by unfold completePartite; simp only [eq_comm]

private lemma sum_completePartite_mul {k : ℕ} (i : Fin k) (f : Fin k → ℝ) :
    ∑ z, completePartite k i z * f z = (∑ z, f z) - f i := by
  have h : ∀ z, completePartite k i z * f z = f z - if i = z then f z else 0 := fun z => by
    unfold completePartite; split_ifs <;> ring
  rw [Finset.sum_congr rfl fun z _ => h z, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ i)]

lemma degree_completePartite {k : ℕ} (i : Fin k) :
    degree (completePartite k) (uniformFin k) i = (k - 1 : ℝ) / k := by
  rw [degree, integral_uniformFin]
  have := sum_completePartite_mul i (fun _ => (1 : ℝ))
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  rw [this]; ring

lemma edgeDensity_completePartite {k : ℕ} (hk : k ≠ 0) :
    edgeDensity (completePartite k) (uniformFin k) = 1 - 1 / k := by
  rw [edgeDensity, mean, integral_uniformFin]
  simp only [degree_completePartite, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  field_simp

/-- Closed form of the kernel powers of `W_k`: `compPow … n` is the `(n+1)`-fold product. -/
lemma compPow_completePartite {k : ℕ} (hk : k ≠ 0) (n : ℕ) (i j : Fin k) :
    compPow (uniformFin k) (completePartite k) n i j =
      ((k - 1 : ℝ) ^ (n + 1) - (-1) ^ (n + 1)) / (k : ℝ) ^ (n + 1) +
        if i = j then (-1 : ℝ) ^ (n + 1) / (k : ℝ) ^ n else 0 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  induction n generalizing i j with
  | zero =>
      show completePartite k i j = _
      unfold completePartite
      split_ifs <;> field_simp <;> ring
  | succ n ih =>
      show ∫ z, completePartite k i z * compPow (uniformFin k) (completePartite k) n z j
          ∂(uniformFin k) = _
      rw [integral_uniformFin]
      simp only [ih]
      rw [sum_completePartite_mul i]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Finset.sum_ite_eq', if_pos (Finset.mem_univ j)]
      split_ifs <;> field_simp <;> ring

/-- Equation `eq:intro-kpartite-value`: `t(C_m, W_k) = ((k-1)/k)^m + (k-1)(-1/k)^m`. -/
theorem cycleDensity_completePartite {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m) :
    cycleDensity (uniformFin k) (completePartite k) m =
      ((k - 1 : ℝ) / k) ^ m + (k - 1 : ℝ) * (-1 / (k : ℝ)) ^ m := by
  have hk0 : k ≠ 0 := by omega
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk0
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [cycleDensity, trace, integral_uniformFin, Nat.add_sub_cancel]
  simp only [compPow_completePartite hk0, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [div_pow, div_pow]
  field_simp
  ring

/-- For odd `m`, the value is the right-hand side of Theorem 1.1 at `p = 1 - 1/k`. -/
theorem cycleDensity_completePartite_odd {k m : ℕ} (hk : 1 ≤ k) (hm : Odd m) :
    cycleDensity (uniformFin k) (completePartite k) m =
      (1 - 1 / (k : ℝ)) ^ m - (1 - 1 / (k : ℝ)) * (1 - (1 - 1 / (k : ℝ))) ^ (m - 1) := by
  have hm1 : 1 ≤ m := by rcases hm with ⟨t, rfl⟩; omega
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [cycleDensity_completePartite hk hm1]
  obtain ⟨t, rfl⟩ := hm
  rw [show 2 * t + 1 - 1 = 2 * t by omega]
  rw [show (-1 / (k : ℝ)) ^ (2 * t + 1) = -(1 / (k : ℝ)) ^ (2 * t + 1) by
      rw [neg_div, Odd.neg_pow ⟨t, rfl⟩]]
  rw [show (1 : ℝ) - (1 - 1 / k) = 1 / k by ring, show (1 : ℝ) - 1 / k = (k - 1) / k by
      field_simp]
  rw [pow_succ (1 / (k : ℝ)) (2 * t)]
  field_simp
  ring

/-- **Corollary 1.2**, minimality: for every `k ≥ 2` and odd `m ≥ 3`, the balanced complete
`k`-partite graphon minimises the `C_m`-density among graphons of edge density `1 - 1/k`. -/
theorem completePartite_minimises {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {W : Ω → Ω → ℝ} {k m : ℕ} (hk : 2 ≤ k) (hm : Odd m)
    (hm3 : 3 ≤ m) (hW : IsGraphon W μ) (hp : edgeDensity W μ = 1 - 1 / k) :
    cycleDensity (uniformFin k) (completePartite k) m ≤ cycleDensity μ W m := by
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · obtain rfl : k = 2 := by omega
    have h0 : cycleDensity (uniformFin 2) (completePartite 2) m = 0 := by
      rw [cycleDensity_completePartite (by norm_num) (by omega)]
      obtain ⟨t, rfl⟩ := hm
      rw [show (-1 / ((2 : ℕ) : ℝ)) ^ (2 * t + 1) = -(1 / ((2 : ℕ) : ℝ)) ^ (2 * t + 1) by
        rw [neg_div, Odd.neg_pow ⟨t, rfl⟩]]
      norm_num
    rw [h0]
    exact trace_compPow_nonneg hW (m - 1)
  · have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
    have hp23 : 2 / 3 ≤ edgeDensity W μ := by
      rw [hp]
      have : 1 / (k : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hk'
      linarith
    rw [cycleDensity_completePartite_odd (by omega) hm, ← hp]
    exact DenseRegion.dense_region_cycle_bound_unconditional hW hp23 hm hm3

end OddCycleBound
