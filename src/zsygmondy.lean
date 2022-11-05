import ring_theory.polynomial.cyclotomic.basic
import ring_theory.polynomial.cyclotomic.eval
import algebra
import tactic
import cyclotomic

variables {a n : ℕ}

theorem exists_prime_of_order (hn : 1 < n) (ha : 1 < a) 
(h_exception_1 : ¬(n = 2 ∧ (∃ (s : ℕ), a = 2 ^ s - 1))) 
(h_exception_2 : ¬(n = 6 ∧ a = 2)) : ∃ (p : ℕ) (h_coprime : (a.coprime p)), 
(nat.prime p) ∧ order_of(zmod.unit_of_coprime a h_coprime) = n :=
begin
  by_contra,
  simp only [not_exists, not_and] at h,
  have hpos_n : 0 < n := by {transitivity 1, exact zero_lt_one, exact hn, },
  let Φ := (polynomial.eval ↑a (polynomial.cyclotomic n ℤ)).to_nat,
  have h_one_le_a_int : 1 ≤ (a : ℤ) := by linarith,
  have h_Phi : 1 < Φ,
  {
    simp only [int.lt_to_nat, nat.cast_one],
    let a' := (a : ℤ),
    have h_a' : ↑a = a' := by refl,
    rw h_a',
    have h_one_lt_a' : 1 < a' := by linarith,
    have h_one_le : 1 ≤ (a' - 1) ^ (n.totient),
    {
      apply one_le_pow_of_one_le,
      linarith,
    },
    exact lt_of_le_of_lt h_one_le (X_sub_one_pow_le_cyclotomic hn h_one_lt_a'),
  },
  have h_one_le : ∀ (k : ℕ), 1 ≤ a ^ k,
  { 
    intro k,
    apply nat.one_le_pow,
    apply nat.pos_of_ne_zero,
    intro h,
    subst h,
    linarith,
  },
  cases h_primes : Φ.factors with p others,
  { rw nat.factors_eq_nil at h_primes, cases h_primes, linarith, linarith, },
  have h_p_in_factors : p ∈ Φ.factors := by { rw h_primes, exact list.mem_cons_self p _},
  have h_p_prime : p.prime := by exact nat.prime_of_mem_factors h_p_in_factors,
  have h_coprime : ∀ (d : ℕ) (h_dvd : d ∣ Φ), a.coprime d,
  {
    intros d h_dvd,
    have h_dvd' : d ∣ a ^ n - 1,
    {
      apply nat.dvd_trans h_dvd _,
      rw ← int.coe_nat_dvd,
      have h_one_le_pow : 1 ≤ a ^ n := 
      by exact one_le_pow_of_one_le (le_of_lt ha) n,
      have h_one_lt_coe_a : 1 < (a : ℤ) := by linarith,
      have h_eq_eval : (a : ℤ) ^ n - 1 = polynomial.eval (a : ℤ) (polynomial.X ^ n - 1) :=
      by simp only [polynomial.eval_sub, polynomial.eval_pow, polynomial.eval_X, polynomial.eval_one],
      rw [int.coe_nat_sub h_one_le_pow, int.coe_nat_pow, nat.cast_one,
      int.to_nat_of_nonneg (polynomial.cyclotomic_nonneg n (le_of_lt h_one_lt_coe_a)),
      h_eq_eval],
      exact polynomial.eval_dvd (polynomial.cyclotomic.dvd_X_pow_sub_one n ℤ),
    },
    cases h_dvd' with t h_dvd',
    have h_pos_t : 0 < t,
    {
      apply nat.pos_of_ne_zero,
      intro h,
      subst h,
      simp only [mul_zero, tsub_eq_zero_iff_le, 
      pow_le_one_iff (nat_ne_zero_of_pos hpos_n)] at h_dvd',
      linarith,
    },
    have h_dvd_t : t ∣ a ^ n - 1 := by { rw h_dvd', exact dvd_mul_left t d },
    have h_div : (a ^ n - 1) / t = d := by exact nat.div_eq_of_eq_mul_left h_pos_t h_dvd',
    rw ← h_div,
    apply nat.coprime.coprime_div_right _ h_dvd_t,
    have h_a_pow_sub_one_eq : a ^ n - 1 = (a ^ (n - 1) - 1) * a + (a - 1),
    {
      apply int.coe_nat_inj,
      rw [int.coe_nat_sub (h_one_le n), int.coe_nat_add, int.coe_nat_mul,
      int.coe_nat_sub (h_one_le (n - 1)), int.coe_nat_sub (le_of_lt ha),
      int.coe_nat_pow, int.coe_nat_pow, int.coe_nat_one, sub_mul,
      one_mul, sub_add_sub_cancel, sub_left_inj, ← nat.sub_add_cancel (le_of_lt hn),
      pow_add, pow_one, nat.add_succ_sub_one, add_zero],
    },
    have h_a_eq : a - 1 + 1 = a := by exact nat.sub_add_cancel (le_of_lt ha),
    have h_cancel : a - 1 + 1 - 1 = a - 1 := 
    by rw [nat.add_succ_sub_one, add_zero],
    rw [h_a_pow_sub_one_eq, 
    nat.coprime_mul_right_add_right a (a - 1) (a ^ (n - 1) - 1),
    nat.coprime_comm, ← h_a_eq, h_cancel, 
    nat.coprime_self_add_right],
    exact nat.coprime_one_right (a - 1),
  },
  have h_order_ne_n : ¬order_of 
  (zmod.unit_of_coprime a (h_coprime p (nat.dvd_of_mem_factors h_p_in_factors))) = n :=
  by exact h p (h_coprime p (nat.dvd_of_mem_factors h_p_in_factors)) h_p_prime,
  have h_p_dvd : p ∣ n,
  {
    by_contra h_not_dvd,
    apply h_order_ne_n,
    have h_p_prime_fact : fact (p.prime) := by { rw fact_iff, exact h_p_prime },
    have h_p_dvd_int : ↑p ∣ polynomial.eval ↑a (polynomial.cyclotomic n ℤ),
    {
      cases nat.dvd_of_mem_factors h_p_in_factors with t h_phi_eq,
      use ↑t,
      rw [← int.coe_nat_mul, ← h_phi_eq, 
      int.to_nat_of_nonneg (polynomial.cyclotomic_nonneg n h_one_le_a_int)],
    }, 
    have h_order_is_n' : ∃ (h_coprime : a.coprime p),
    order_of(zmod.unit_of_coprime a h_coprime) = n := 
    by exact order_of_eq_iff_is_root_of_cyclotomic 
    h_p_prime_fact h_not_dvd hpos_n (ne_of_lt ha) h_p_dvd_int,
    cases h_order_is_n',
    exact h_order_is_n'_h,
  },
  sorry,
end