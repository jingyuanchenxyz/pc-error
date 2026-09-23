import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Kronecker's lemma

If `∑ x i / i` converges then `(1/p) ∑_{i ≤ p} x i → 0`.  This is the deterministic half of
Kolmogorov's strong law (Fact 1): the probabilistic half gives almost sure convergence of
the series `∑ (X i - E X i)/i`, and Kronecker's lemma turns it into convergence of the
Cesàro averages.

The proof is summation by parts: with `s p = ∑_{i ∈ Icc 1 p} x i / i`,

  `∑_{i ∈ Icc 1 p} x i = p * s p - ∑_{i ∈ range p} s i`,

so `(1/p) ∑_{i ∈ Icc 1 p} x i = s p - (1/p) ∑_{i ∈ range p} s i → S - S = 0`, the second
term by Cesàro convergence.
-/

open Filter Finset
open scoped Topology

namespace PCError

/-- Summation by parts for `∑_{i ∈ Icc 1 p} x i` in terms of the partial sums of `x i / i`. -/
lemma sum_Icc_eq_mul_sub_sum (x : ℕ → ℝ) (p : ℕ) :
    ∑ i ∈ Finset.Icc 1 p, x i =
      (p : ℝ) * (∑ i ∈ Finset.Icc 1 p, x i / i) -
        ∑ i ∈ Finset.range p, ∑ j ∈ Finset.Icc 1 i, x j / j := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hp1 : ((p : ℝ) + 1) ≠ 0 := by positivity
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_Icc_succ_top (by omega),
      Finset.sum_range_succ]
    push_cast
    field_simp
    ring

/-- **Kronecker's lemma.**  If the series `∑ x i / i` converges, the Cesàro averages of `x`
tend to zero. -/
theorem kronecker {x : ℕ → ℝ} {S : ℝ}
    (h : Tendsto (fun p => ∑ i ∈ Finset.Icc 1 p, x i / i) atTop (𝓝 S)) :
    Tendsto (fun p : ℕ => (1 / (p : ℝ)) * ∑ i ∈ Finset.Icc 1 p, x i) atTop (𝓝 0) := by
  set s : ℕ → ℝ := fun p => ∑ i ∈ Finset.Icc 1 p, x i / i with hs
  have hces : Tendsto (fun p : ℕ => ((p : ℝ))⁻¹ * ∑ i ∈ Finset.range p, s i) atTop (𝓝 S) :=
    h.cesaro
  have hdiff : Tendsto (fun p : ℕ => s p - ((p : ℝ))⁻¹ * ∑ i ∈ Finset.range p, s i) atTop
      (𝓝 (S - S)) := h.sub hces
  rw [sub_self] at hdiff
  refine hdiff.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with p hp
  have hp' : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
  rw [sum_Icc_eq_mul_sub_sum x p]
  field_simp
  ring

end PCError
