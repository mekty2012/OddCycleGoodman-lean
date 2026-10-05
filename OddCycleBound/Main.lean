import OddCycleBound.DenseRegion.Diagonal.DenseRegionEndgame
import OddCycleBound.DenseRegion.Diagonal.Regularity
import OddCycleBound.ShortCycles
import OddCycleBound.KPartite
import OddCycleBound.Equality.Uniqueness
import OddCycleBound.IntermediateRegion.IntermediateAssembly

open MeasureTheory

namespace OddCycleBound

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {W : Ω → Ω → ℝ}

theorem dense_cycle_bound {m : ℕ} (hW : IsGraphon W μ) (hp : 2 / 3 ≤ edgeDensity W μ)
    (hm : Odd m) (hm3 : 3 ≤ m) :
    cycleDensity μ W m ≥
      edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) :=
  DenseRegion.dense_region_cycle_bound_unconditional hW hp hm hm3

/-- **Theorem 1.1** (odd-cycle Goodman bound for `p ≥ 2/3`). -/
theorem dense_region_main_theorem {m : ℕ} (hW : IsGraphon W μ) (hp : 2 / 3 ≤ edgeDensity W μ)
    (hm : Odd m) (hm3 : 3 ≤ m) :
    cycleDensity μ W m ≥
      edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) :=
  dense_cycle_bound hW hp hm hm3

/-- **Theorem 1.3** (strengthened extended commonality), for `p ≥ 2/3` and every odd `m ≥ 3`. -/
theorem strengthened_commonality_bound {m : ℕ} (hW : IsGraphon W μ)
    (hp : 2 / 3 ≤ edgeDensity W μ) (hm : Odd m) (hm3 : 3 ≤ m) :
    cycleDensity μ W m + cycleDensity μ (compl W) m ≥
      edgeDensity W μ ^ m + (1 - edgeDensity W μ) ^ m +
        (pathDensity (compl W) μ (m - 1) - (1 - edgeDensity W μ) ^ (m - 1)) :=
  DenseRegion.dense_region_commonality_bound hW hp hm hm3

/-- **Theorem 1.3** for `m ∈ {3, 5, 7}` and `p ≥ 1/2` (Proposition 4.1). -/
theorem strengthened_commonality_bound_short {m : ℕ} (hW : IsGraphon W μ)
    (hm : m = 3 ∨ m = 5 ∨ m = 7) (hp : 1 / 2 ≤ edgeDensity W μ) :
    cycleDensity μ W m + cycleDensity μ (compl W) m ≥
      edgeDensity W μ ^ m + (1 - edgeDensity W μ) ^ m +
        (pathDensity (compl W) μ (m - 1) - (1 - edgeDensity W μ) ^ (m - 1)) :=
  commonality_short hW hm hp

/-- **Proposition 6.1**, equation `eq:degree-variance-gap`: for `p ≥ 2/3` the gap `Ψ_m(W)` in
Theorem 1.3 is at least `(m - 1) (∫ (d_W - p)²)^((m-1)/2)`. -/
theorem commonality_gap_ge_degree_variance {m : ℕ} (hW : IsGraphon W μ)
    (hp : 2 / 3 ≤ edgeDensity W μ) (hm : Odd m) (hm3 : 3 ≤ m) :
    cycleDensity μ W m + cycleDensity μ (compl W) m - pathDensity (compl W) μ (m - 1)
        - (edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1)) ≥
      (m - 1 : ℝ) * (∫ x, (degree W μ x - edgeDensity W μ) ^ 2 ∂μ) ^ ((m - 1) / 2) :=
  DenseRegion.commonality_gap_ge_degree_variance hW hp hm hm3

/-- **Proposition 6.1**: for `p ≥ 2/3`, equality holds in Theorem 1.3 if and only if `W` is
a.e. `p`-regular. -/
theorem commonality_eq_iff_regular {m : ℕ} (hW : IsGraphon W μ)
    (hp : 2 / 3 ≤ edgeDensity W μ) (hm : Odd m) (hm3 : 3 ≤ m) :
    cycleDensity μ W m + cycleDensity μ (compl W) m - pathDensity (compl W) μ (m - 1)
        - (edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1)) = 0 ↔
      ∀ᵐ x ∂μ, degree W μ x = edgeDensity W μ :=
  DenseRegion.commonality_eq_iff_regular hW hp hm hm3

theorem intermediate_cycle_bound {m : ℕ} (hW : IsGraphon W μ) (hm : Odd m) (hm11 : 11 ≤ m)
    (hp : edgeDensity W μ < 2 / 3) :
    cycleDensity μ W m ≥
      edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) := by
  by_cases hp2 : edgeDensity W μ ≤ 1 / 2
  · have hnonneg : (0 : ℝ) ≤ cycleDensity μ W m := trace_compPow_nonneg hW (m - 1)
    linarith [rhs_nonpos_of_le_half hW (by omega : 1 ≤ m) hp2]
  ·
    have hp1 : (1 : ℝ) / 2 < edgeDensity W μ := not_le.mp hp2
    have hm9 : 9 ≤ m := by omega
    exact IntermediateRegion.intermediateRegion_odd_cycle_bound hW hm hm9 hp1 hp

theorem small_cycle_bound {m : ℕ} (hW : IsGraphon W μ) (hm : Odd m) (hm3 : 3 ≤ m) (hm9 : m ≤ 9) :
    cycleDensity μ W m ≥
      edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) := by
  obtain ⟨k, rfl⟩ := hm
  have hk1 : 1 ≤ k := by omega
  have hk4 : k ≤ 4 := by omega
  interval_cases k
  · exact cycle_bound_short_all hW (Or.inl rfl)
  · exact cycle_bound_short_all hW (Or.inr (Or.inl rfl))
  · exact cycle_bound_short_all hW (Or.inr (Or.inr rfl))
  ·
    show cycleDensity μ W 9 ≥ edgeDensity W μ ^ 9 - edgeDensity W μ * (1 - edgeDensity W μ) ^ 8
    by_cases hp : 2 / 3 ≤ edgeDensity W μ
    ·
      exact dense_cycle_bound hW hp ⟨4, rfl⟩ (by norm_num)
    · by_cases hp2 : edgeDensity W μ ≤ 1 / 2
      ·
        have hnonneg : 0 ≤ cycleDensity μ W 9 := trace_compPow_nonneg hW 8
        have hrhs := rhs_nonpos_of_le_half hW (m := 9) (by norm_num) hp2
        norm_num at hrhs
        linarith
      ·
        exact IntermediateRegion.intermediateRegion_odd_cycle_bound hW ⟨4, by norm_num⟩
          (by norm_num) (not_le.mp hp2) (not_le.mp hp)

theorem odd_cycle_bound {m : ℕ} (hW : IsGraphon W μ) (hm : Odd m) (hm3 : 3 ≤ m) :
    cycleDensity μ W m ≥
      edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) := by
  by_cases hm9 : m ≤ 9
  · exact small_cycle_bound hW hm hm3 hm9
  · have hm11 : 11 ≤ m := by rcases hm with ⟨k, rfl⟩; omega
    by_cases hp : 2 / 3 ≤ edgeDensity W μ
    · exact dense_cycle_bound hW hp hm hm3
    · exact intermediate_cycle_bound hW hm hm11 (not_le.mp hp)

universe u

/-- The results of the paper in one universe-polymorphic statement:
Theorem 1.1; Theorem 1.3 for `p ≥ 2/3` and, for `m ∈ {3, 5, 7}`, for `p ≥ 1/2`; equation
`eq:intro-kpartite-value`; Corollary 1.2 (minimality for `k ≥ 2`, uniqueness for `k ≥ 3`, the
latter being Proposition 6.2); and Proposition 6.1. -/
theorem main_results :
    -- Theorem 1.1
    (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (W : Ω → Ω → ℝ) (m : ℕ), IsGraphon W μ → 2 / 3 ≤ edgeDensity W μ → Odd m → 3 ≤ m →
        cycleDensity μ W m ≥
          edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1)) ∧
    -- Theorem 1.3, `p ≥ 2/3`
    (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (W : Ω → Ω → ℝ) (m : ℕ), IsGraphon W μ → 2 / 3 ≤ edgeDensity W μ → Odd m → 3 ≤ m →
        cycleDensity μ W m + cycleDensity μ (compl W) m ≥
          edgeDensity W μ ^ m + (1 - edgeDensity W μ) ^ m +
            (pathDensity (compl W) μ (m - 1) - (1 - edgeDensity W μ) ^ (m - 1))) ∧
    -- Theorem 1.3, `m ∈ {3, 5, 7}` and `p ≥ 1/2`
    (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (W : Ω → Ω → ℝ) (m : ℕ), IsGraphon W μ → (m = 3 ∨ m = 5 ∨ m = 7) →
        1 / 2 ≤ edgeDensity W μ →
        cycleDensity μ W m + cycleDensity μ (compl W) m ≥
          edgeDensity W μ ^ m + (1 - edgeDensity W μ) ^ m +
            (pathDensity (compl W) μ (m - 1) - (1 - edgeDensity W μ) ^ (m - 1))) ∧
    -- equation `eq:intro-kpartite-value`
    (∀ k m : ℕ, 1 ≤ k → 1 ≤ m →
        cycleDensity (uniformFin k) (completePartite k) m =
          ((k - 1 : ℝ) / k) ^ m + (k - 1 : ℝ) * (-1 / (k : ℝ)) ^ m) ∧
    -- Corollary 1.2, minimality
    (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (W : Ω → Ω → ℝ) (k m : ℕ), 2 ≤ k → Odd m → 3 ≤ m → IsGraphon W μ →
        edgeDensity W μ = 1 - 1 / k →
        cycleDensity (uniformFin k) (completePartite k) m ≤ cycleDensity μ W m) ∧
    -- Corollary 1.2, uniqueness (Proposition 6.2)
    (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (W : Ω → Ω → ℝ) (m : ℕ), Odd m → 3 ≤ m → IsGraphon W μ →
        2 / 3 ≤ edgeDensity W μ → edgeDensity W μ < 1 →
        cycleDensity μ W m =
          edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) →
        ∃ k : ℕ, 3 ≤ k ∧ edgeDensity W μ = 1 - 1 / k ∧
          ∃ φ : Ω → Fin k, Measurable φ ∧ Measure.map φ μ = uniformFin k ∧
            ∀ᵐ x ∂(μ.prod μ), W x.1 x.2 = completePartite k (φ x.1) (φ x.2)) ∧
    -- Proposition 6.1
    (∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (W : Ω → Ω → ℝ) (m : ℕ), IsGraphon W μ → 2 / 3 ≤ edgeDensity W μ → Odd m → 3 ≤ m →
        (cycleDensity μ W m + cycleDensity μ (compl W) m - pathDensity (compl W) μ (m - 1)
            - (edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1)) ≥
          (m - 1 : ℝ) * (∫ x, (degree W μ x - edgeDensity W μ) ^ 2 ∂μ) ^ ((m - 1) / 2)) ∧
        (cycleDensity μ W m + cycleDensity μ (compl W) m - pathDensity (compl W) μ (m - 1)
            - (edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1)) = 0 ↔
          ∀ᵐ x ∂μ, degree W μ x = edgeDensity W μ)) :=
  ⟨fun _ _ _ _ hW hp hm hm3 => dense_region_main_theorem hW hp hm hm3,
    fun _ _ _ _ hW hp hm hm3 => strengthened_commonality_bound hW hp hm hm3,
    fun _ _ _ _ hW hm hp => strengthened_commonality_bound_short hW hm hp,
    fun _ _ hk hm => cycleDensity_completePartite hk hm,
    fun _ _ _ _ _ hk hm hm3 hW hp => completePartite_minimises hk hm hm3 hW hp,
    fun _ _ _ _ hm hm3 hW hp hp1 heq => completePartite_unique hm hm3 hW hp hp1 heq,
    fun _ _ _ _ hW hp hm hm3 =>
      ⟨commonality_gap_ge_degree_variance hW hp hm hm3, commonality_eq_iff_regular hW hp hm hm3⟩⟩

end OddCycleBound
