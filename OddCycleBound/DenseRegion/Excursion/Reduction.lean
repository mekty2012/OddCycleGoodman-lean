import OddCycleBound.DenseRegion.Excursion.Projections
import OddCycleBound.Excursion.Bijections

/-!
# Excursion expansions (Lemmas 3.1, 3.2, 3.3)

* `cycleDensity_excursions` (Lemma `lem:cycle-excursions`): expanding the `m`-fold kernel product
  over words, the all-`P` word gives `q^m`, the all-`Q` word gives `τ = Tr(A^m)`, and the words
  with `r ≥ 1` excursions contribute `(m/r) ∑_{tuples} q^{∑α} ∏ gᵀ A^{βᵢ} g`, by the marked-word
  count (`sum_numMarks_eq`), the bijection with block-length tuples (`sum_pq_eq_sum_tuples`) and the
  block evaluation (`applyWord_blockWord`).
* `pathDensity_excursions` (Lemma `lem:path-excursions`): the same for paths, with fixed endpoints.
* `neckSum_eq_baseline_add_momentPhi` (Lemma `lem:polynomial-reduction`): adding the cycle
  expansions of `W` and `U = 1 - W`, where the all-`Q` words cancel because `m` is odd, and
  subtracting the path expansion gives `p^m + q^m - q^{m-1} + Φ_m`.
-/

open MeasureTheory
open scoped BigOperators

namespace OddCycleBound.DenseRegion

open Excursion

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {V W : Ω → Ω → ℝ}

/-! ### Evaluation of traces of words -/

lemma trace_listKer_false_cons (hV : IsGraphon V μ) (l : List Bool) (x : Ω) :
    trace μ (listKer V μ (false :: l)) = applyWord V μ (false :: l) (fun _ => 1) x := by
  rw [applyWord_false_cons hV l]

lemma trace_listKer_blockWord (hV : IsGraphon V μ) {t : List (ℕ × ℕ)} (ht : t ≠ []) :
    trace μ (listKer V μ (blockWord t)) =
      tupleWeight (edgeDensity V μ) (specMoment V μ) t := by
  obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure μ
  obtain ⟨p, t', rfl⟩ := List.exists_cons_of_ne_nil ht
  set l := List.replicate p.1 false ++ List.replicate (p.2 + 1) true ++ blockWord t' with hldef
  have hl : blockWord (p :: t') = false :: l := by
    rw [blockWord_cons, blk, List.replicate_succ, hldef]
    simp
  rw [hl, trace_listKer_false_cons hV l x, ← hl]
  have h2 := congrFun (applyWord_blockWord hV 0 (p :: t')) x
  rw [List.replicate_zero, List.append_nil] at h2
  rw [h2, pow_zero, one_mul]

lemma trace_listKer_replicate_false (hV : IsGraphon V μ) (n : ℕ) :
    trace μ (listKer V μ (List.replicate (n + 1) false)) = edgeDensity V μ ^ (n + 1) := by
  obtain ⟨x⟩ := nonempty_of_isProbabilityMeasure μ
  rw [List.replicate_succ, trace_listKer_false_cons hV _ x, ← List.replicate_succ,
    applyWord_replicate_false hV, mul_one]

/-! ### Cycle densities by excursions (Lemma 3.1) -/

/-- The words with no excursions are the two constant words. -/
lemma filter_numMarks_eq_zero (n : ℕ) :
    Finset.univ.filter (fun v : Fin (n + 1) → Bool => numMarks v = 0) =
      {fun _ => false, fun _ => true} := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · exact eq_const_of_numMarks_eq_zero
  · rintro (rfl | rfl) <;>
    · rw [numMarks, Finset.card_eq_zero, marks, Finset.filter_eq_empty_iff]
      intro j _ hj
      simp [IsMark] at hj

lemma sum_pq_marks (hV : IsGraphon V μ) {n r : ℕ} (hr : 1 ≤ r) :
    ∑ v ∈ Finset.univ.filter (fun v : Fin (n + 1) → Bool => IsMark v 0 ∧ numMarks v = r),
        trace μ (listKer V μ (List.ofFn v)) =
      if 2 * r ≤ n + 1 then tupleSum (edgeDensity V μ) (specMoment V μ) r (n + 1 - 2 * r)
      else 0 := by
  classical
  have hbridge : ∑ v ∈ Finset.univ.filter
      (fun v : Fin (n + 1) → Bool => IsMark v 0 ∧ numMarks v = r),
        trace μ (listKer V μ (List.ofFn v)) =
      ∑ l ∈ (allWords (n + 1)).filter (fun l => IsPQ l ∧ qpCount l + 1 = r),
        trace μ (listKer V μ l) := by
    rw [Finset.sum_filter, Finset.sum_filter, ← sum_fin_eq_sum_allWords]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hiff : (IsMark v 0 ∧ numMarks v = r) ↔
        (IsPQ (List.ofFn v) ∧ qpCount (List.ofFn v) + 1 = r) := by
      rw [numMarks_eq]
      constructor
      · rintro ⟨h1, h2⟩
        rw [if_pos h1] at h2
        exact ⟨(isMark_zero_iff v).mp h1, by omega⟩
      · rintro ⟨h1, h2⟩
        have h1' := (isMark_zero_iff v).mpr h1
        rw [if_pos h1']
        exact ⟨h1', by omega⟩
    simp only [hiff]
  rw [hbridge]
  split_ifs with h2r
  · rw [sum_pq_eq_sum_tuples hr h2r, tupleSum]
    refine Finset.sum_congr rfl fun t ht => ?_
    have hne : t ≠ [] := by
      rintro rfl; rw [mem_tuples] at ht; simp at ht; omega
    exact trace_listKer_blockWord hV hne
  · refine Finset.sum_eq_zero fun l hl => ?_
    exfalso
    rw [Finset.mem_filter, mem_allWords] at hl
    obtain ⟨hlen, hpq, hqp⟩ := hl
    obtain ⟨t, hne, rfl⟩ := blockWord_of_pq hpq.1 hpq.2
    rw [qpCount_blockWord hne] at hqp
    rw [length_blockWord] at hlen
    omega

/-- **Lemma 3.1** (`lem:cycle-excursions`), in moment form: with `q = edgeDensity V`,
`s = specMoment V` and `τ` the trace of the all-`Q` word,
`t(C_{n+1}, V) = q^{n+1} + τ + ∑_{r ≥ 1, 2r ≤ n+1} ((n+1)/r) ∑_{tuples} q^{∑α} ∏ s(βᵢ)`. -/
theorem cycleDensity_excursions (hV : IsGraphon V μ) (n : ℕ) :
    cycleDensity μ V (n + 1) =
      edgeDensity V μ ^ (n + 1) + trace μ (listKer V μ (List.replicate (n + 1) true)) +
        ∑ k ∈ Finset.range (n + 1),
          if 2 * (k + 1) ≤ n + 1 then
            ((n + 1 : ℝ) / (k + 1 : ℕ)) *
              tupleSum (edgeDensity V μ) (specMoment V μ) (k + 1) (n + 1 - 2 * (k + 1))
          else 0 := by
  classical
  set F : (Fin (n + 1) → Bool) → ℝ := fun v => trace μ (listKer V μ (List.ofFn v)) with hF
  have hrot : ∀ j v, F (rot j v) = F v := fun j v => trace_listKer_ofFn_rot hV j v
  rw [cycleDensity_eq_sum_words hV (by omega), ← sum_fin_eq_sum_allWords]
  change ∑ v, F v = _
  rw [← Finset.sum_fiberwise_of_maps_to (g := numMarks) (t := Finset.range (n + 2))
    (fun v _ => by
      rw [Finset.mem_range, numMarks]
      have := Finset.card_le_univ (marks v)
      rw [Fintype.card_fin] at this
      omega)]
  rw [Finset.sum_range_succ', filter_numMarks_eq_zero,
    Finset.sum_pair (by
      intro h
      have := congrFun h 0
      simp at this)]
  have hP : F (fun _ => false) = edgeDensity V μ ^ (n + 1) := by
    simp only [hF, List.ofFn_const]
    exact trace_listKer_replicate_false hV n
  have hQ : F (fun _ => true) = trace μ (listKer V μ (List.replicate (n + 1) true)) := by
    simp only [hF, List.ofFn_const]
  rw [hP, hQ, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  have hcount := sum_numMarks_eq (k + 1) F hrot
  rw [sum_pq_marks hV (by omega)] at hcount
  have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  split_ifs at hcount ⊢ with h2r
  · rw [div_mul_eq_mul_div, eq_div_iff hk]
    linarith
  · rw [mul_zero] at hcount
    exact (mul_eq_zero.mp hcount).resolve_left hk

/-! ### Path densities by excursions (Lemma 3.2) -/

lemma kernelOp_finset_sum (hV : IsGraphon V μ) {ι : Type*} (s : Finset ι) {f : ι → Ω → ℝ}
    (hf : ∀ i ∈ s, Good (f i)) (x : Ω) :
    kernelOp V μ (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, kernelOp V μ (f i) x := by
  simp only [kernelOp, Finset.mul_sum]
  exact integral_finsetSum s fun i hi => integrable_Uf hV (hf i hi) x

/-- The path expansion over words: `T_V^k 1 = ∑_{words of length k} (R₁ M_V ⋯ R_k M_V) 1`. -/
lemma pathIter_eq_sum_words (hV : IsGraphon V μ) : ∀ k : ℕ,
    pathIter V μ k = fun x => ∑ w ∈ allWords k, applyWord V μ w (fun _ => 1) x
  | 0 => by
      funext x
      simp [allWords, listsOf, applyWord, pathIter]
  | k + 1 => by
      funext x
      show kernelOp V μ (pathIter V μ k) x = _
      rw [pathIter_eq_sum_words hV k,
        kernelOp_finset_sum hV _ fun w _ => good_applyWord hV good_one w, sum_allWords_succ]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [kernelOp_eq_kerP_add_kerQ hV (good_applyWord hV good_one w)]
      rfl

lemma mean_compress (hV : IsGraphon V μ) {f : Ω → ℝ} (hf : Good f) :
    mean μ (compress V μ f) = 0 := by
  unfold mean compress
  rw [integral_sub (good_kernelOp hV hf).integrable (integrable_const _)]
  simp [mean]

lemma mean_applyWord_true_cons (hV : IsGraphon V μ) (l : List Bool) :
    mean μ (applyWord V μ (true :: l) (fun _ => 1)) = 0 := by
  show mean μ (kernelOp (kerQ V μ) μ (applyWord V μ l fun _ => 1)) = 0
  rw [kernelOp_kerQ hV (good_applyWord hV good_one l)]
  exact mean_compress hV (good_applyWord hV good_one l)

lemma sum_range_ite_le (K c : ℕ) (f : ℕ → ℝ) :
    ∑ N ∈ Finset.range (K + 1), (if c + N ≤ K then f N else 0) =
      if c ≤ K then ∑ N ∈ Finset.range (K - c + 1), f N else 0 := by
  rw [← Finset.sum_filter]
  split_ifs with hc
  · refine Finset.sum_congr ?_ fun _ _ => rfl
    ext N; simp only [Finset.mem_filter, Finset.mem_range]; omega
  · refine Finset.sum_eq_zero fun N hN => ?_
    simp only [Finset.mem_filter] at hN; omega

/-- **Lemma 3.2** (`lem:path-excursions`), in moment form:
`t(P_k, V) = ∑_{r, 2r ≤ k} ∑_j h_{k-2r-j}(q^{×(r+1)}) · momentConv s r j`. -/
theorem pathDensity_excursions (hV : IsGraphon V μ) (k : ℕ) :
    pathDensity V μ k = ∑ r ∈ Finset.range (k + 1),
      if 2 * r ≤ k then
        conv (fun d => hsym (List.replicate (r + 1) (edgeDensity V μ)) d)
          (momentConv (specMoment V μ) r) (k - 2 * r)
      else 0 := by
  classical
  have hsum : pathDensity V μ k =
      ∑ w ∈ allWords k, mean μ (applyWord V μ w (fun _ => 1)) := by
    rw [pathDensity, pathIter_eq_sum_words hV k, mean]
    exact integral_finsetSum _ fun w _ => (good_applyWord hV good_one w).integrable
  rw [hsum, ← Finset.sum_filter_add_sum_filter_not (allWords k) (fun l => l.head? ≠ some true)]
  have hzero : ∑ w ∈ (allWords k).filter (fun l => ¬ l.head? ≠ some true),
      mean μ (applyWord V μ w (fun _ => 1)) = 0 := by
    refine Finset.sum_eq_zero fun w hw => ?_
    rw [Finset.mem_filter, not_not] at hw
    obtain ⟨l, rfl⟩ : ∃ l, w = true :: l := by
      cases w with
      | nil => simp at hw
      | cons b l => simp at hw; exact ⟨l, by rw [hw.2]⟩
    exact mean_applyWord_true_cons hV l
  rw [hzero, add_zero, sum_head_ne_true_eq]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hinner : ∀ N, (∑ t ∈ tuples r N, mean μ (applyWord V μ
      (blockWord t ++ List.replicate (k - 2 * r - N) false) fun _ => 1)) =
      edgeDensity V μ ^ (k - 2 * r - N) * tupleSum (edgeDensity V μ) (specMoment V μ) r N := by
    intro N
    rw [tupleSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [applyWord_blockWord hV, mean_const]
  simp only [hinner]
  rw [show (fun N => if 2 * r + N ≤ k then edgeDensity V μ ^ (k - 2 * r - N) *
      tupleSum (edgeDensity V μ) (specMoment V μ) r N else 0) =
      fun N => if 2 * r + N ≤ k then edgeDensity V μ ^ (k - 2 * r - N) *
      tupleSum (edgeDensity V μ) (specMoment V μ) r N else 0 from rfl, sum_range_ite_le]
  split_ifs with h2r
  · rw [List.replicate_succ, hsym_cons_eq_conv, conv_assoc, ← tupleSum_eq, conv_comm]
    unfold conv
    refine Finset.sum_congr rfl fun N hN => ?_
    rw [Finset.mem_range] at hN
    rw [show k - 2 * r - N = k - 2 * r - N from rfl]
    ring
  · rfl

/-! ### The reduction to excursion polynomials (Lemma 3.3) -/

lemma momentConv_neg_pow (s : ℕ → ℝ) : ∀ r j : ℕ,
    momentConv (fun i => (-1 : ℝ) ^ i * s i) r j = (-1 : ℝ) ^ j * momentConv s r j
  | 0, j => by cases j <;> simp [momentConv]
  | r + 1, j => by
      rw [momentConv_succ, momentConv_succ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      rw [momentConv_neg_pow s r (j - i),
        show (-1 : ℝ) ^ j = (-1) ^ i * (-1) ^ (j - i) by rw [← pow_add]; congr 1; omega]
      ring

lemma tupleSum_eq_choose (q : ℝ) (s : ℕ → ℝ) {r : ℕ} (hr : r ≠ 0) (n : ℕ) :
    tupleSum q s r n = ∑ j ∈ Finset.range (n + 1),
      (Nat.choose (n - j + (r - 1)) (r - 1) : ℝ) * q ^ (n - j) * momentConv s r j := by
  rw [tupleSum_eq, conv_comm]
  unfold conv
  refine Finset.sum_congr rfl fun j _ => ?_
  dsimp only
  rw [hsym_replicate' q hr]
  ring

lemma conv_hsym_succ_eq (q : ℝ) (s : ℕ → ℝ) (r n : ℕ) (hn : 1 ≤ n) :
    conv (fun d => hsym (List.replicate (r + 1) q) d) (momentConv s r) (n - 1) =
      ∑ j ∈ Finset.range (n + 1),
        (if j < n then (Nat.choose (n - 1 - j + r) r : ℝ) * q ^ (n - 1 - j) else 0) *
          momentConv s r j := by
  rw [conv_comm]
  unfold conv
  rw [show n - 1 + 1 = n by omega, Finset.sum_range_succ, if_neg (lt_irrefl n), zero_mul,
    add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_range] at hj
  dsimp only
  rw [if_pos hj, hsym_replicate' q (Nat.succ_ne_zero r), Nat.succ_sub_one]
  ring

lemma listKer_compl_replicate_true (hW : IsGraphon W μ) : ∀ k : ℕ,
    listKer W μ (List.replicate (k + 1) true) =
      fun x y => (-1 : ℝ) ^ (k + 1) * listKer (compl W) μ (List.replicate (k + 1) true) x y := by
  have hQ : kerQ W μ = fun x y => -kerQ (compl W) μ x y := by
    funext x y
    simp only [kerQ, DenseRegion.degree_compl hW, compl]
    ring
  intro k
  induction k with
  | zero =>
      funext x y
      show kerQ W μ x y = (-1 : ℝ) ^ (0 + 1) * kerQ (compl W) μ x y
      rw [hQ]; ring
  | succ k ih =>
      show comp μ (letterKer W μ true) (listKer W μ (List.replicate (k + 1) true)) =
        fun x y => (-1 : ℝ) ^ (k + 2) * comp μ (letterKer (compl W) μ true)
          (listKer (compl W) μ (List.replicate (k + 1) true)) x y
      rw [ih]
      show comp μ (kerQ W μ) _ = _
      rw [hQ, comp_neg_left, comp_smul_right]
      funext x y
      show -((-1 : ℝ) ^ (k + 1) * comp μ (kerQ (compl W) μ)
          (listKer (compl W) μ (List.replicate (k + 1) true)) x y) =
        (-1 : ℝ) ^ (k + 2) * comp μ (kerQ (compl W) μ)
          (listKer (compl W) μ (List.replicate (k + 1) true)) x y
      ring

lemma sum_range_ite_two_mul_le (R : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.range (2 * R + 1), (if 2 * (k + 1) ≤ 2 * R + 1 then f k else 0) =
      ∑ k ∈ Finset.range R, f k := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma sum_range_ite_two_mul_le' (R : ℕ) (f : ℕ → ℝ) :
    ∑ r ∈ Finset.range (2 * R + 1), (if 2 * r ≤ 2 * R then f r else 0) =
      f 0 + ∑ k ∈ Finset.range R, f (k + 1) := by
  rw [← Finset.sum_filter]
  rw [show (Finset.range (2 * R + 1)).filter (fun r => 2 * r ≤ 2 * R) = Finset.range (R + 1) by
    ext r; simp only [Finset.mem_filter, Finset.mem_range]; omega]
  rw [Finset.sum_range_succ', add_comm]

lemma conv_hsym_one_momentConv_zero (q : ℝ) (s : ℕ → ℝ) (n : ℕ) :
    conv (fun d => hsym (List.replicate (0 + 1) q) d) (momentConv s 0) n = q ^ n := by
  unfold conv
  rw [Finset.sum_eq_single n]
  · simp
  · intro i hi hin
    rw [Finset.mem_range] at hi
    obtain ⟨j, hj⟩ : ∃ j, n - i = j + 1 := ⟨n - i - 1, by omega⟩
    rw [hj, momentConv_zero_succ, mul_zero]
  · intro h; simp at h

/-- **Lemma 3.3** (`lem:polynomial-reduction`): adding the cycle expansions of `W` and of
`U = 1 - W` (the all-`Q` words cancel because `m` is odd) and subtracting the path expansion of
`U` gives `t(C_m, W) + t(C_m, U) - t(P_{m-1}, U) = p^m + q^m - q^{m-1} + Φ_m`
(equation `eq:commonality-gap`), with `Φ_m = momentPhi m q (specMoment U)`. -/
theorem neckSum_eq_baseline_add_momentPhi (hW : IsGraphon W μ) {m : ℕ}
    (hm : Odd m) (hm3 : 3 ≤ m) :
    neckSum W μ m =
      edgeDensity W μ ^ m - edgeDensity W μ * (1 - edgeDensity W μ) ^ (m - 1) +
      momentPhi m (1 - edgeDensity W μ) (specMoment (compl W) μ) := by
  have hU := isGraphon_compl hW
  set p := edgeDensity W μ with hp
  set q := 1 - p with hq
  set s := specMoment (compl W) μ with hs
  have hqU : edgeDensity (compl W) μ = q := edgeDensity_compl hW
  have hsW : specMoment W μ = fun j => (-1 : ℝ) ^ j * s j := by
    funext j
    rw [hs, specMoment_compl hW j, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    norm_num
  have hid := cycleDensity_eq_neckSum_add hW hm hm3
  obtain ⟨R, rfl⟩ := hm
  have hR : 1 ≤ R := by omega
  have hCU := cycleDensity_excursions hU (2 * R)
  have hCW := cycleDensity_excursions hW (2 * R)
  have hPU := pathDensity_excursions hU (2 * R)
  have hτ : trace μ (listKer W μ (List.replicate (2 * R + 1) true)) =
      -trace μ (listKer (compl W) μ (List.replicate (2 * R + 1) true)) := by
    rw [listKer_compl_replicate_true hW (2 * R)]
    simp only [trace]
    rw [integral_const_mul, Odd.neg_one_pow ⟨R, rfl⟩]
    ring
  rw [hqU, sum_range_ite_two_mul_le, ← hs] at hCU
  rw [hsW, sum_range_ite_two_mul_le, ← hp] at hCW
  rw [hqU, sum_range_ite_two_mul_le', conv_hsym_one_momentConv_zero, ← hs, Nat.mul_zero,
    Nat.sub_zero] at hPU
  rw [show 2 * R + 1 - 1 = 2 * R by omega] at hid ⊢
  have hphi : momentPhi (2 * R + 1) q s = ∑ k ∈ Finset.range R,
      momentPhiTerm (2 * R + 1) (k + 1) q s := by
    unfold momentPhi
    rw [show (2 * R + 1 - 1) / 2 = R by omega]
  rw [hphi]
  have hterm : ∀ k ∈ Finset.range R,
      (((2 * R : ℕ) : ℝ) + 1) / ((k + 1 : ℕ) : ℝ) *
          tupleSum p (fun j => (-1 : ℝ) ^ j * s j) (k + 1) (2 * R + 1 - 2 * (k + 1)) +
        (((2 * R : ℕ) : ℝ) + 1) / ((k + 1 : ℕ) : ℝ) *
          tupleSum q s (k + 1) (2 * R + 1 - 2 * (k + 1)) -
        conv (fun d => hsym (List.replicate (k + 1 + 1) q) d) (momentConv s (k + 1))
          (2 * R - 2 * (k + 1)) =
      momentPhiTerm (2 * R + 1) (k + 1) q s := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hn1 : 1 ≤ 2 * R + 1 - 2 * (k + 1) := by omega
    rw [show 2 * R - 2 * (k + 1) = 2 * R + 1 - 2 * (k + 1) - 1 by omega,
      conv_hsym_succ_eq q s (k + 1) _ hn1,
      tupleSum_eq_choose p _ (Nat.succ_ne_zero k), tupleSum_eq_choose q s (Nat.succ_ne_zero k)]
    unfold momentPhiTerm momentShiftTerm momentPathTerm
    simp only [momentConv_neg_pow, Nat.add_sub_cancel]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hp' : p = 1 - q := by rw [hq]; ring
    rw [hp']
    push_cast
    ring
  have hsum := Finset.sum_congr (s₁ := Finset.range R) rfl hterm
  rw [← hsum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hsplit : q ^ (2 * R + 1) = q * q ^ (2 * R) := by ring
  linarith [hid, hCU, hCW, hPU, hτ, hsplit]

end OddCycleBound.DenseRegion
