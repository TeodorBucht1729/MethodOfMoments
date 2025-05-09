import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Polynomial.Basic

noncomputable section

namespace MeasureTheory


def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε


variable {a b : ℝ} {μ : ProbabilityMeasure (Set.Icc a b)} {μs : ℕ → ProbabilityMeasure (Set.Icc a b)}

lemma integrable_of_continuous (f : C(Set.Icc a b, ℝ)) (μ : ProbabilityMeasure (Set.Icc a b)) : Integrable f μ := by
  apply Continuous.integrable_of_hasCompactSupport
  exact f.continuous_toFun
  exact HasCompactSupport.of_compactSpace f

lemma monomials_integrable_lemma (j : ℕ) (c : ℝ) (μ : ProbabilityMeasure (Set.Icc a b)) : Integrable (fun x : Set.Icc a b => c * x^j) μ := by
  let cm := ContinuousMap.restrict (Set.Icc a b) ⟨fun x => (Polynomial.monomial j c).eval x, Polynomial.continuous (Polynomial.monomial j c)⟩
  have eq_cm : (fun x : Set.Icc a b => c * x.val^j) = cm.toFun := by
    dsimp [cm]
    simp
    rfl
  apply Continuous.integrable_of_hasCompactSupport
  rw [eq_cm]
  exact cm.continuous_toFun
  rw [eq_cm]
  exact HasCompactSupport.of_compactSpace cm

theorem method_of_moments
  (hm : ∀ (k : ℕ), ConvergesTo (fun (n : ℕ) => ∫ x , x^k ∂(μs n).val) (∫ x , x^k ∂μ.val)) :
  ∀ (f : BoundedContinuousFunction ℝ ℝ), ConvergesTo (fun (n : ℕ) => ∫ x, (f.restrict (Set.Icc a b))  x ∂(μs n)) (∫ x, (f.restrict (Set.Icc a b)) x ∂μ) := by
  intro f
  dsimp [ConvergesTo]
  intro ε epos

  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b f (Continuous.continuousOn f.continuous_toFun) (ε/3) (by linarith)

  let coeff_sum := ∑ j ∈ p.support, |p.coeff j|

  have coeff_sum_larger : ∀ j ∈ p.support, |p.coeff j| ≤ coeff_sum := by
    intro j
    apply Finset.single_le_sum
    intro i i_in
    apply abs_nonneg

  have coeff_sum_nonneg : 0 ≤ coeff_sum := by
    apply Finset.sum_nonneg
    intro j j_in
    apply abs_nonneg

  have coeff_sum_pos :  0 < (coeff_sum + 1) := by
    linarith

  let δ : ℝ := ε/(3 * (p.support.card + 1) * (coeff_sum + 1))

  have deltapos : δ > 0 := by
    apply div_pos
    linarith
    apply mul_pos
    apply mul_pos
    linarith
    linarith
    exact coeff_sum_pos

  dsimp [ConvergesTo] at hm

  let get_kth_N := fun (k : ℕ) => Classical.choose (hm k δ deltapos)
  let get_kth_proof := fun (k : ℕ) => Classical.choose_spec (hm k δ deltapos)

  let Nk_sum := ∑ k ∈ p.support, get_kth_N k
  have Nk_sum_le_summand : ∀ k ∈ p.support, get_kth_N k ≤ Nk_sum := by
    intro k k_in
    apply Finset.single_le_sum
    intro i i_in
    apply zero_le
    exact k_in

  have bigN : ∃ (N: ℕ), ∀ k ∈ p.support, ∀ n ≥ N, |(∫ x , x^k ∂(μs n).val : ℝ) - (∫ x , x^k ∂μ.val : ℝ)| < δ := by
    use Nk_sum
    intro k k_in n ngeqN
    have : n ≥ get_kth_N k := by
      apply le_trans (Nk_sum_le_summand k k_in) ngeqN
    exact get_kth_proof k n this


  obtain ⟨N, bigN_proof⟩ := bigN
  use N
  intro n ngeqN

  let pr : C(Set.Icc a b, ℝ) := ContinuousMap.restrict (Set.Icc a b) ⟨fun x => p.eval x, Polynomial.continuous p⟩

  have pr_eval_eq_sum : ∀ x : Set.Icc a b, pr x = ∑ j ∈ p.support, p.coeff j * (x : ℝ)^j := by
    intro x
    dsimp [pr]
    have pr_eq : pr x = p.eval (x : ℝ) := by
      rfl
    rw [Polynomial.eval_eq_sum]
    dsimp [Polynomial.sum]

  let fr := f.restrict (Set.Icc a b)
  let rr : C(Set.Icc a b, ℝ) := fr - pr

  have fr_decomp : ∀ x, fr x = pr x + rr x := by
    intro x
    dsimp [rr]
    linarith

  have rr_small : (x : Set.Icc a b) → |rr x| < ε / 3 := by
    intro x
    have rr_eq : rr x = fr x - pr x := by
      rfl
    rw [rr_eq]
    have rr_eq1 : |fr x - pr x| = |pr x - fr x| := by
      exact abs_sub_comm (fr x) (pr x)
    have rr_eq2 : |fr x - pr x| = |f x - p.eval x.val| := by
      dsimp [pr]
      exact rfl
    rw [rr_eq2, abs_sub_comm]
    exact hp x.val x.property

  have pr_integrable : Integrable (pr) μ := integrable_of_continuous pr μ
  have rr_integrable : Integrable rr μ := integrable_of_continuous rr μ
  have pr_integrable_n : Integrable (pr) (μs n) := integrable_of_continuous pr (μs n)
  have rr_integrable_n : Integrable rr (μs n) := integrable_of_continuous rr (μs n)

  -- let monomial_restricted : ℕ → ℝ → C(Set.Icc a b, ℝ) := fun j c => ContinuousMap.restrict (Set.Icc a b) ⟨fun x => (Polynomial.monomial j c).eval x, Polynomial.continuous (Polynomial.monomial j c)⟩
  -- what does the below notation actually mean? Why is it different from the notation fun j c => (...)
  have monomial_integrable : {j : ℕ} →  {c : ℝ} → Integrable (fun x : Set.Icc a b => c * x.val^j) μ := by
    intro j c
    exact monomials_integrable_lemma j c μ

  have monomial_integrable_n : {j : ℕ} → {c : ℝ} → Integrable (fun x : Set.Icc a b => c * x.val^j) (μs n) := by
    intro j c
    exact monomials_integrable_lemma j c (μs n)

  have triangle_integral_ineq : |(∫ x , fr x ∂(μs n).val : ℝ) - (∫ x , fr x ∂μ.val : ℝ)| < ε := by
    calc
    |(∫ x , fr x ∂(μs n).val : ℝ) - (∫ x , fr x ∂μ.val : ℝ)| =
      |(∫ x , (pr x : ℝ) + rr x ∂(μs n).val : ℝ) - (∫ x , (pr x : ℝ) + rr x ∂μ.val : ℝ)| := by
      simp_rw [fr_decomp]
    _ = |(∫ x , pr x ∂(μs n).val : ℝ) - (∫ x , pr x ∂μ.val : ℝ)
     + ((∫ x , rr x ∂(μs n).val : ℝ) - (∫ x , rr x ∂μ.val : ℝ))| := by
      apply congr_arg
      rw [integral_add, integral_add]
      linarith
      exact pr_integrable
      exact rr_integrable
      exact pr_integrable_n
      exact rr_integrable_n
    _ ≤ |(∫ x , pr x ∂(μs n).val : ℝ) - (∫ x , pr x ∂μ.val : ℝ)| + |(∫ x , rr x ∂(μs n).val : ℝ) - (∫ x , rr x ∂μ.val : ℝ)| := by
      apply abs_add
    _ ≤ ∑ x ∈ p.support, |(∫ (a_1 : ↑(Set.Icc a b)), p.coeff x * ↑a_1 ^ x ∂↑(μs n) - ∫ (a_1 : ↑(Set.Icc a b)), p.coeff x * ↑a_1 ^ x ∂↑μ)|
    + |(∫ x , rr x ∂(μs n).val : ℝ) - (∫ x , rr x ∂μ.val : ℝ)| := by
      apply add_le_add
      simp_rw [pr_eval_eq_sum]
      rw [MeasureTheory.integral_finset_sum, MeasureTheory.integral_finset_sum]
      rw [← Finset.sum_sub_distrib]
      apply Finset.abs_sum_le_sum_abs
      intro j j_in
      apply monomial_integrable
      intro i i_in
      apply monomial_integrable_n
      rfl
    _ ≤ ∑ j ∈ p.support, |p.coeff j| * |(∫ x , x^j ∂(μs n).val : ℝ) - (∫ x , x^j ∂μ.val : ℝ)|
    + |(∫ x , rr x ∂(μs n).val : ℝ) - (∫ x , rr x ∂μ.val : ℝ)| := by
      apply add_le_add
      apply Finset.sum_le_sum
      intro j j_in
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      rw [← mul_sub_left_distrib]
      rw [abs_mul]
      rfl
      rfl
    _ ≤ ∑ j ∈ p.support, |p.coeff j| * |(∫ x , x^j ∂(μs n).val : ℝ) - (∫ x , x^j ∂μ.val : ℝ)|
    + |(∫ x , rr x ∂(μs n).val : ℝ)| + |(∫ x , rr x ∂μ.val : ℝ)| := by
      rw [add_assoc]
      apply add_le_add
      rfl
      apply abs_sub
    _ < ∑ j ∈ p.support, |p.coeff j| * |(∫ x , x^j ∂(μs n).val : ℝ) - (∫ x , x^j ∂μ.val : ℝ)|
    + ε / 3 + ε / 3 := by
      rw [add_assoc, add_assoc]
      nth_rewrite 1 [add_comm]
      nth_rewrite 3 [add_comm]
      apply add_lt_add_of_lt_of_le
      apply add_lt_add

      calc
        |∫ (x : ↑(Set.Icc a b)), rr x ∂↑(μs n)| ≤ ∫ (x : ↑(Set.Icc a b)), |rr x| ∂(μs n) := by
          apply MeasureTheory.abs_integral_le_integral_abs
        _ < ε/3 := by
          obtain ⟨x, xprop⟩ := MeasureTheory.exists_integral_le (MeasureTheory.Integrable.abs rr_integrable_n)
          apply lt_of_lt_of_le' (rr_small x) xprop
      calc
        |∫ (x : ↑(Set.Icc a b)), rr x ∂↑μ| ≤ ∫ (x : ↑(Set.Icc a b)), |rr x| ∂μ := by
          apply MeasureTheory.abs_integral_le_integral_abs
        _ < ε/3 := by
          obtain ⟨x, xprop⟩ := MeasureTheory.exists_integral_le (MeasureTheory.Integrable.abs rr_integrable)
          apply lt_of_lt_of_le' (rr_small x) xprop
      rfl
    _ ≤ ∑ j ∈ p.support, |p.coeff j| * |(∫ x , x^j ∂(μs n).val : ℝ) - (∫ x , x^j ∂μ.val : ℝ)| + 2 * ε/3 := by
      linarith
    _ ≤ ∑ j ∈ p.support, |p.coeff j| * δ + 2 * ε/3 := by
      apply add_le_add
      apply Finset.sum_le_sum
      intro j j_in
      apply mul_le_mul
      rfl
      exact le_of_lt (bigN_proof j j_in n ngeqN)
      apply abs_nonneg
      apply abs_nonneg
      rfl
    _ ≤ ε/3 + 2 * ε/3 := by
      apply add_le_add
      calc
          ∑ j ∈ p.support, |p.coeff j| * δ ≤ ∑ j ∈ p.support, coeff_sum * δ := by
            apply Finset.sum_le_sum
            intro j j_in
            apply mul_le_mul
            apply coeff_sum_larger j j_in
            repeat linarith
          _ = p.support.card * coeff_sum * δ := by
            rw [Finset.sum_const]
            simp
            linarith
          _ = p.support.card * coeff_sum * ε/(3 * (p.support.card + 1) * (coeff_sum + 1)) := by
            dsimp [δ]
            rw [mul_div_assoc]
          _ = (p.support.card / (p.support.card + 1)) * (coeff_sum / (coeff_sum + 1)) * (ε / 3) := by
            field_simp -- field_simp was very helpful here
            left
            linarith
          _ ≤ 1 * (coeff_sum / (coeff_sum + 1)) * (ε / 3) := by
            rw [mul_assoc, mul_assoc]
            apply mul_le_mul
            have psuppcardpos : (0 : ℝ) < p.support.card + 1 := by linarith
            apply (@div_le_one _ _ _ _ (p.support.card : ℝ) (p.support.card + 1 : ℝ) psuppcardpos).2
            linarith
            rfl
            apply mul_nonneg
            apply div_nonneg
            repeat linarith
          _ = (coeff_sum / (coeff_sum + 1)) * (ε / 3) := by
            rw [one_mul]
          _ ≤ ε / 3 := by
            nth_rw 2 [← one_mul ε]
            rw [mul_div_assoc]
            apply mul_le_mul
            apply (@div_le_one _ _ _ _ (coeff_sum : ℝ) (coeff_sum + 1 : ℝ) coeff_sum_pos).2
            linarith
            rfl
            repeat linarith
      rfl
    _ = ε := by linarith

  exact triangle_integral_ineq
