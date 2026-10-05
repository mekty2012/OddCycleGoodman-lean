import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace OddCycleBound.IntermediateRegion

open Set

def bernsteinP9 (s : ℝ) : ℝ :=
  10395 / 128 * s ^ 9 - 333333 / 2048 * s ^ 8 + 13635 / 128 * s ^ 7 + 51005 / 2048 * s ^ 6
    - 18765 / 128 * s ^ 5 + 264969 / 2048 * s ^ 4 - 4995 / 64 * s ^ 3 + 11913 / 256 * s ^ 2
    - 135 / 8 * s + 3

theorem bernsteinP9_pos {s : ℝ} (hs : s ∈ Icc (0 : ℝ) (1 / 2)) : 0 < bernsteinP9 s := by
  obtain ⟨h0, h1⟩ := hs
  have hA : (0 : ℝ) ≤ 2 * s := by linarith
  have hB : (0 : ℝ) ≤ 1 - 2 * s := by linarith

  have term : ∀ (c : ℝ) (i j : ℕ), 0 ≤ c → 0 ≤ c * (2 * s) ^ i * (1 - 2 * s) ^ j :=
    fun c i j hc => mul_nonneg (mul_nonneg hc (pow_nonneg hA i)) (pow_nonneg hB j)

  have key : bernsteinP9 s = 1 / 2
      + (3 - 1 / 2) * 1 * (2 * s) ^ 0 * (1 - 2 * s) ^ 9
      + (33 / 16 - 1 / 2) * 9 * (2 * s) ^ 1 * (1 - 2 * s) ^ 8
      + (17795 / 12288 - 1 / 2) * 36 * (2 * s) ^ 2 * (1 - 2 * s) ^ 7
      + (29843 / 28672 - 1 / 2) * 84 * (2 * s) ^ 3 * (1 - 2 * s) ^ 6
      + (361761 / 458752 - 1 / 2) * 126 * (2 * s) ^ 4 * (1 - 2 * s) ^ 5
      + (918263 / 1376256 - 1 / 2) * 126 * (2 * s) ^ 5 * (1 - 2 * s) ^ 4
      + (7142309 / 11010048 - 1 / 2) * 84 * (2 * s) ^ 6 * (1 - 2 * s) ^ 3
      + (1096445 / 1572864 - 1 / 2) * 36 * (2 * s) ^ 7 * (1 - 2 * s) ^ 2
      + (390495 / 524288 - 1 / 2) * 9 * (2 * s) ^ 8 * (1 - 2 * s) ^ 1
      + (361511 / 524288 - 1 / 2) * 1 * (2 * s) ^ 9 * (1 - 2 * s) ^ 0 := by
    unfold bernsteinP9; ring
  linarith [key,
    term (((3 : ℝ) - 1 / 2) * 1) 0 9 (by norm_num),
    term (((33 : ℝ) / 16 - 1 / 2) * 9) 1 8 (by norm_num),
    term (((17795 : ℝ) / 12288 - 1 / 2) * 36) 2 7 (by norm_num),
    term (((29843 : ℝ) / 28672 - 1 / 2) * 84) 3 6 (by norm_num),
    term (((361761 : ℝ) / 458752 - 1 / 2) * 126) 4 5 (by norm_num),
    term (((918263 : ℝ) / 1376256 - 1 / 2) * 126) 5 4 (by norm_num),
    term (((7142309 : ℝ) / 11010048 - 1 / 2) * 84) 6 3 (by norm_num),
    term (((1096445 : ℝ) / 1572864 - 1 / 2) * 36) 7 2 (by norm_num),
    term (((390495 : ℝ) / 524288 - 1 / 2) * 9) 8 1 (by norm_num),
    term (((361511 : ℝ) / 524288 - 1 / 2) * 1) 9 0 (by norm_num)]

end OddCycleBound.IntermediateRegion
