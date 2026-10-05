import OddCycleBound.Necklace

open MeasureTheory
open scoped BigOperators

namespace OddCycleBound.DenseRegion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → Ω → ℝ}

noncomputable def neckSum (W : Ω → Ω → ℝ) (μ : Measure Ω) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m - 1),
    (-1 : ℝ) ^ j * pairing μ (pathIter (compl W) μ j) (complIter (compl W) μ (m - 1 - j))

theorem cycleDensity_eq_neckSum_add (hW : IsGraphon W μ) {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    cycleDensity μ W m
      = neckSum W μ m + (pathDensity (compl W) μ (m - 1) - cycleDensity μ (compl W) m) := by
  have hV : IsGraphon (compl W) μ := isGraphon_compl hW
  have hcc : compl (compl W) = W := by funext x y; simp only [compl]; ring
  have hn : m - 2 + 1 = m - 1 := by omega
  have hev : Even (m - 1) := by rcases hm with ⟨k, hk⟩; exact ⟨k, by omega⟩
  have key := complTrace_necklace hV (m - 2)
  rw [hn, hcc, hev.neg_one_pow, one_mul] at key
  exact key

theorem cycle_ge_neckSum (hW : IsGraphon W μ) {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) :
    neckSum W μ m ≤ cycleDensity μ W m := by
  have hdel := edge_deletion_general (isGraphon_compl hW) (m - 2)
  rw [show m - 2 + 2 = m from by omega, show m - 2 + 1 = m - 1 from by omega] at hdel
  linarith [cycleDensity_eq_neckSum_add hW hm hm3]

theorem commonality_of_neckSum_ge (hW : IsGraphon W μ) {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m)
    (hneck : edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1)
              ≤ neckSum W μ m) :
    cycleDensity μ W m + cycleDensity μ (compl W) m ≥
      edgeDensity W μ ^ m + (1 - edgeDensity W μ) ^ m +
        (pathDensity (compl W) μ (m - 1) - (1 - edgeDensity W μ) ^ (m - 1)) := by
  have hsplit : (1 - edgeDensity W μ) ^ m - (1 - edgeDensity W μ) ^ (m - 1)
      = -(edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1)) := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    ring
  linarith [cycleDensity_eq_neckSum_add hW hm hm3]

theorem cycle_bound_of_neckSum (hW : IsGraphon W μ) {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m)
    (hpos : edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1)
              ≤ neckSum W μ m) :
    edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1)
      ≤ cycleDensity μ W m :=
  hpos.trans (cycle_ge_neckSum hW hm hm3)

end OddCycleBound.DenseRegion
