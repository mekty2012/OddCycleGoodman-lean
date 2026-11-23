# OddCycleBound

A Lean 4 / Mathlib formalization of the **odd-cycle Goodman bound** and the results around it in
the paper *Goodman-type lower bounds for odd cycles I: The dense regime*.
For every graphon `W` with edge density `p` and every odd `m ≥ 3`,

```
t(C_m, W)  ≥  p^m − p·(1 − p)^(m − 1).
```

The development is complete and `sorry`-free.

## Notation

For a probability space `(Ω, μ)` and a symmetric measurable `W : Ω → Ω → ℝ` with values in `[0,1]`:

- `IsGraphon W μ` — `W` is a graphon (measurable, symmetric, `0 ≤ W ≤ 1`). Graphons live on an
  arbitrary probability space, not only on `[0,1]`.
- `edgeDensity W μ` — the edge density `p = ∫∫ W`.
- `compl W` — the complementary graphon `1 − W`.
- `cycleDensity μ W m` — the `m`-cycle density `t(C_m, W)`, defined as the trace of the
  `m`-fold kernel product, i.e. `trace μ (compPow μ W (m - 1)) = ∫ (W^{∘m})(x, x) dμ(x)`
  (`compPow μ W n` is the `(n+1)`-fold product).
- `pathDensity W μ k` — the density `t(P_k, W)` of the path with `k` edges.
- `completePartite k`, `uniformFin k` — the balanced complete `k`-partite graphon, modelled on
  `Fin k` with the uniform probability measure (the paper's `W_k` on `[0,1]` is its pullback along
  `x ↦ ⌈kx⌉`).

## Headline theorems

All of these are available after `import OddCycleBound.Main`. `OddCycleBound/CheckComplete.lean`
prints the axioms of the results of the paper and of `odd_cycle_bound`, which uses the other
results covering all edge densities.

Results of the paper (all for odd `m ≥ 3`):

- **`dense_region_main_theorem`** (inequality in Theorem 1.1; alias of `dense_cycle_bound`) — for
  `p ≥ 2/3`, `cycleDensity μ W m ≥ p^m − p(1 − p)^(m − 1)`.
- **`strengthened_commonality_bound`** (inequality in Theorem 1.2) — for `p ≥ 2/3`,
  `t(C_m, W) + t(C_m, 1−W) ≥ p^m + (1−p)^m + (t(P_{m−1}, 1−W) − (1−p)^(m−1))`.
- **`strengthened_commonality_bound_short`** (inequality in Theorem 1.2 via Proposition 5.1) — the
  same inequality for `m ∈ {3, 5, 7}` and `p ≥ 1/2`.
- **`cycleDensity_completePartite`** (equation `eq:intro-kpartite-value`) —
  `t(C_m, W_k) = ((k−1)/k)^m + (k−1)(−1/k)^m` (for every `m ≥ 1`).
- **`completePartite_minimises`** (from Theorem 1.1 and equation `eq:intro-kpartite-value`) — for
  every `k ≥ 2`, `W_k` minimises the `C_m`-density among graphons of edge density `1 − 1/k`. The
  case `k = 2` is trivial because `t(C_m, W_2) = 0`.
- **`completePartite_unique`** (Proposition 7.2, equality case of Theorem 1.1) — if
  `2/3 ≤ p < 1` and equality holds in Theorem 1.1, then `p = 1 − 1/k` for an integer `k ≥ 3`,
  and `W` is almost everywhere the pullback of `completePartite k` along a measurable
  measure-preserving map `φ : Ω → Fin k`. Conversely (`pullback_attains_bound`) every such
  pullback attains equality, and densities are invariant under such pullbacks
  (`cycleDensity_pullback`, for `m ≥ 2`).
- **`commonality_gap_ge_degree_variance`**, **`commonality_eq_iff_regular`** (Proposition 7.1) —
  for `p ≥ 2/3` the gap in Theorem 1.2 is at least `(m−1)(∫ (d_W − p)²)^((m−1)/2)`, and it
  vanishes if and only if `W` is a.e. `p`-regular, which is the equality case of Theorem 1.2.
- **`main_results`** — all of the above bundled in one universe-polymorphic statement.

The qualitative stability statement (Corollary 7.3) is not formalised. The case `p = 1` of the
equality statement in Theorem 1.1, where `W = 1` a.e., has no separate Lean statement.

Results covering all edge densities (together with the companion paper):

- **`odd_cycle_bound`** — for any graphon `W` and any odd `m ≥ 3`,
  `cycleDensity μ W m ≥ p^m − p(1 − p)^(m − 1)`. Assembled by dispatching on `m` and `p`:
  `m ≤ 9` → `small_cycle_bound`; else `p ≥ 2/3` → `dense_cycle_bound`,
  `p < 2/3` → `intermediate_cycle_bound`.
- **`small_cycle_bound`** — `3 ≤ m ≤ 9`, every `p`. For `m = 3, 5, 7` this follows from
  Proposition 5.1 (`cycle_bound_short_all`); `m = 9` splits on `p`.
- **`intermediate_cycle_bound`** — `p < 2/3`, odd `m ≥ 11` (companion paper; trivial for
  `p ≤ 1/2`).

## Layout

- `Graphon.lean`, `PathDensity.lean`, `Kernel.lean`, `Cycle.lean`, `Necklace.lean`,
  `BasicBounds.lean` — graphons, kernels and their products, traces, path and cycle densities.
- `DenseRegion/` — the dense regime.
  - `GraphonReduction.lean` — `neckSum W μ m`, which equals `t(C_m,W) + t(C_m,U) − t(P_{m−1},U)`
    with `U = 1 − W` (`cycleDensity_eq_neckSum_add`), and the reduction of Theorems 1.1 and 1.2
    to a lower bound for it.
  - `Excursion/Projections.lean`, `Excursion/Reduction.lean` — Section 4: the kernels of `P M_V`
    and `Q M_V`, the expansion of kernel powers over words, cyclicity of the trace, block
    evaluation, and Lemmas 4.1–4.3 (`neckSum_eq_baseline_add_momentPhi`).
  - `MomentExpansion.lean`, `GraphonKrylovBridge.lean`, `KrylovCompression.lean`,
    `AtomicMomentRepresentation.lean`, `AtomicSpectral.lean` — the operator form of Section 3: the
    centred operator, the bound `‖A‖ ≤ 1/2`, and the finitely supported measure reproducing the
    moments `gᵀAʲg`.
  - `Expansion.lean`, `SymmetricPoly.lean`, `MixtureIntegral.lean`, `KernelForm.lean`,
    `KernelImproper.lean`, `KernelIntegrable.lean`, `RhoLemma.lean`, `Diagonal/` — Section 6 and
    Appendix B (Dirichlet averaging, Beta and Gamma representations, the Gamma moment bound).
  - `ExpansionAssembly.lean`, `Diagonal/DenseRegionEndgame.lean`, `Diagonal/Commonality.lean`,
    `Diagonal/Regularity.lean` — Theorems 1.1 and 1.2, Proposition 7.1.
- `Excursion/` — the combinatorics of Section 4: cyclic words, marks and the marked-word count
  (`Words.lean`), block-length tuples and their weighted sums (`Tuples.lean`), and the bijections
  between words and tuples (`Bijections.lean`).
- `ShortCycles/ExcursionPolynomials.lean`, `ShortCycles.lean` — Section 5 (`C_3, C_5, C_7`).
- `KPartite.lean` — the balanced complete `k`-partite graphon and its minimality.
- `Equality/` — Section 7: the spectral step without eigenvalues (`RegularKernel.lean`,
  `SpectralStep.lean`), the clique decomposition (`Cliques.lean`), and uniqueness
  (`Uniqueness.lean`).
- `General/PathRecurrence.lean`, `Spectral/`, `IntermediateRegion/` — infrastructure and the
  intermediate regime `1/2 < p < 2/3` (companion paper).
- `Main.lean` — the headline theorems; `CheckComplete.lean` — the axiom check.

## How to verify the proof

1. **It compiles.** From this directory:
   ```
   lake exe cache get
   LEAN_NUM_THREADS=3 lake build
   ```
   Most modules depend on all of Mathlib (through `Graphon.lean`), and each Lean process needs
   about 8 GB of committed memory, so on a 16 GB machine limit the parallelism (with
   `LEAN_NUM_THREADS=3`, Lake runs two or three Lean processes at a time; with the default it
   runs out of memory).

2. **It uses only the standard axioms.** `OddCycleBound/CheckComplete.lean` imports `Main.lean`
   and prints the axioms of every headline theorem:
   ```
   LEAN_NUM_THREADS=3 lake build OddCycleBound.CheckComplete
   ```
   Each line must read
   ```
   '…' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```
   the three standard axioms of classical Lean/Mathlib. The absence of `sorryAx` is the
   machine-checked guarantee that nothing is assumed or left unproven.

There are no `decide +kernel` / `native_decide` shortcuts, no computational certificates trusted
outside the kernel, and no `maxHeartbeats` above 1,600,000.

## Benchmarks

A clean build of the project (Mathlib from the cache) takes about 21 minutes (1265 s), and the
axiom check afterwards about 30 seconds. This was measured with `LEAN_NUM_THREADS=3` on a
Windows 11 laptop with 16 GB RAM and an Intel i7-1165G7 CPU (2.80 GHz). The peak total working
set of the Lean processes was about 9.3 GB.
