import ring_theory.polynomial.cyclotomic.basic
import ring_theory.polynomial.cyclotomic.eval
import algebra
import tactic
import cyclotomic
import data.fintype.units
import number_theory.multiplicity

variables {a n : ℕ}

lemma order_of_units_le_totient [ne_zero n] (h_coprime : a.coprime n) : 
order_of (zmod.unit_of_coprime a h_coprime) ≤ n.totient :=
begin
  rw ←zmod.card_units_eq_totient,
  exact order_of_le_card_univ,
end

lemma order_of_units_pos (h_coprime : a.coprime n) : 
0 < order_of (zmod.unit_of_coprime a h_coprime) :=
begin
  sorry,
end

lemma nat_dvd_mul_pow_of_one_le (a b c : ℕ) : 1 ≤ c → a ∣ b * a ^ c :=
begin
  intro h_le,
  use b * a ^ (c - 1),
  rw [mul_comm a _, mul_assoc, mul_eq_mul_left_iff],
  left,
  rw [← nat.sub_add_cancel h_le, pow_add, pow_one, nat.sub_add_cancel h_le],
end

lemma mul_pow_dvd_eq_mul_pow_sub (a b c : ℕ) : 1 ≤ c 
→ a * b ^ c / b = a * b ^ (c - 1) := 
begin
  intro hc,
  sorry,
end

lemma dvd_pow_order_mul_sub_one (a b c : ℕ) (h_coprime : a.coprime b) :
b ∣ a ^ (order_of (zmod.unit_of_coprime a h_coprime) * c) - 1 :=
begin
  sorry,
end

lemma four_dvd_pow_sub_one_of_two_dvd (h_coprime : a.coprime 2) :
2 ∣ n → 4 ∣ a ^ n - 1 :=
begin
  sorry,
end

lemma nat_le_sub_one_of_lt (a b : ℕ) : a < b → a ≤ b - 1 :=
begin
  intro h_lt,
  sorry,
end

lemma nat_multiplicity_self (a : ℕ) : 2 ≤ a → multiplicity a a = 1 :=
begin
  intro ha,
  sorry,
end

lemma sub_one_mul_lt_pow_sub_one (a b : ℕ) : 1 < a → (a - 1) * b < a ^ b - 1 :=
begin
  sorry,
end

lemma nat_pow_le_one_iff (a b : ℕ) : a ^ b ≤ 1 ↔ a ≤ 1 ∨ b = 0 :=
begin
  sorry,
end

lemma order_of_two_mod_three_eq_two (h_coprime : (2 : ℕ).coprime 3) : 
order_of (zmod.unit_of_coprime 2 h_coprime) = 2 :=
begin
  sorry,
end

lemma order_of_eq_one_in_units_two (h_coprime : a.coprime 2) :
order_of (zmod.unit_of_coprime a h_coprime) = 1 :=
begin
  simp only [order_of_eq_one_iff, eq_iff_true_of_subsingleton],
end

lemma le_of_order_mul_pow_eq_order_mul_pow (p q t₁ t₂ : ℕ) 
(h_p_prime : p.prime) (h_q_prime : q.prime) 
(h_p_coprime : a.coprime p) (h_q_coprime : a.coprime q)
(h_one_le_first : 1 ≤ t₁) (h_one_le_second : 1 ≤ t₂) :
order_of (zmod.unit_of_coprime a h_p_coprime) * p ^ t₁ 
= order_of (zmod.unit_of_coprime a h_q_coprime) * q ^ t₂ → p ≤ q :=
begin
  intro h,
  cases em (p = q) with h_eq h_ne,
  { rw h_eq, },
  {
    have h_p_dvd_mul : p ∣ order_of (zmod.unit_of_coprime a h_q_coprime) * q ^ t₂,
    {
      use order_of (zmod.unit_of_coprime a h_p_coprime) * p ^ (t₁ - 1),
      rw [← h, ← mul_assoc, mul_comm p _, mul_assoc, mul_eq_mul_left_iff],
      left,
      rw [← nat.sub_add_cancel h_one_le_first, pow_add, mul_comm,
      pow_one, nat.add_succ_sub_one, add_zero],
    },
    rw nat.prime.dvd_mul h_p_prime at h_p_dvd_mul,
    cases h_p_dvd_mul with h_dvd h_dvd,
    swap,
    {
      exfalso,
      apply h_ne,
      rw ← nat.prime_dvd_prime_iff_eq h_p_prime h_q_prime,
      exact nat.prime.dvd_of_dvd_pow h_p_prime h_dvd,
    },
    {
      transitivity order_of (zmod.unit_of_coprime a h_q_coprime),
      { exact nat.le_of_dvd (order_of_units_pos h_q_coprime) h_dvd, },
      {
        transitivity q - 1,
        {
          rw ← nat.totient_prime h_q_prime,
          haveI : ne_zero q := ⟨ nat.prime.ne_zero h_q_prime ⟩,
          exact order_of_units_le_totient h_q_coprime,
        },
        {
          exact tsub_le_self,
        }
      }
    }
  }
end


theorem exists_prime_of_order (hn : 1 < n) (ha : 1 < a) 
(h_exception_1 : ¬(n = 2 ∧ (∃ (s : ℕ), a = 2 ^ s - 1))) 
(h_exception_2 : ¬(n = 6 ∧ a = 2)) : ∃ (p : ℕ) (h_coprime : (a.coprime p)), 
(nat.prime p) ∧ order_of(zmod.unit_of_coprime a h_coprime) = n :=
begin
  by_contra,
  simp only [not_exists, not_and] at h,
  have hpos_n : 0 < n := by {transitivity 1, exact zero_lt_one, exact hn, },
  set Φ := (polynomial.eval ↑a (polynomial.cyclotomic n ℤ)).to_nat with h_Phi_def,
  have h_one_le_a_int : 1 ≤ (a : ℤ) := by linarith,
  have h_Phi : 1 < Φ,
  {
    simp only [int.lt_to_nat, nat.cast_one],
    set a' := (a : ℤ),
    have h_one_lt_a' : 1 < a' := by linarith,
    have h_one_le : 1 ≤ (a' - 1) ^ (n.totient),
    {
      apply one_le_pow_of_one_le,
      linarith,
    },
    exact lt_of_le_of_lt h_one_le (X_sub_one_pow_lt_cyclotomic hn h_one_lt_a'),
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
  have h_one_lt : ∀ (k : ℕ), 0 < k → 1 < a ^ k,
  { 
    intros k hk,
    exact nat.one_lt_pow k a hk ha,
  },
  have h_one_lt_int : ∀ (k : ℕ), 0 < k → 1 < (a : ℤ) ^ k,
  {
    intros k hk,
    rw [← int.coe_nat_pow, ← nat.cast_one, int.coe_nat_lt],
    exact h_one_lt k hk,
  },
  cases h_primes : Φ.factors with p others,
  { rw nat.factors_eq_nil at h_primes, cases h_primes, linarith, linarith, },
  have h_p_in_factors : p ∈ Φ.factors := by { rw h_primes, exact list.mem_cons_self p _},
  have h_p_prime : p.prime := by exact nat.prime_of_mem_factors h_p_in_factors,
  have h_p_prime_fact : fact (p.prime) := by { rw fact_iff, exact h_p_prime },
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
      by simp only [polynomial.eval_sub, polynomial.eval_pow, 
      polynomial.eval_X, polynomial.eval_one],
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
  have h_a_coprime_p : a.coprime p := by exact h_coprime p (nat.dvd_of_mem_factors h_p_in_factors),
  have h_order_ne_n : ∀ (p' : ℕ) (h_in_factors : p' ∈ Φ.factors), ¬order_of 
  (zmod.unit_of_coprime a (h_coprime p' (nat.dvd_of_mem_factors h_in_factors))) = n :=
  by { intros p' h_in_factors, 
  exact h p' (h_coprime p' (nat.dvd_of_mem_factors h_in_factors)) 
  (nat.prime_of_mem_factors h_in_factors), },
  have h_p_dvd : ∀ (p' : ℕ) (h_in_factors : p' ∈ Φ.factors), p' ∣ n,
  {
    intros p' h_in_factors,
    by_contra h_not_dvd,
    apply h_order_ne_n,
    have h_p'_dvd_int : ↑p' ∣ polynomial.eval ↑a (polynomial.cyclotomic n ℤ),
    {
      cases nat.dvd_of_mem_factors h_in_factors with t h_phi_eq,
      use ↑t,
      rw [← int.coe_nat_mul, ← h_phi_eq, 
      int.to_nat_of_nonneg (polynomial.cyclotomic_nonneg n h_one_le_a_int)],
    },
    have h_p'_prime_fact : fact (p'.prime) := 
    by { rw fact_iff, exact nat.prime_of_mem_factors h_in_factors, },
    have h_order_is_n' : ∃ (h_coprime : a.coprime p'),
    order_of(zmod.unit_of_coprime a h_coprime) = n := 
    by exact order_of_eq_iff_is_root_of_cyclotomic 
    h_p'_prime_fact h_not_dvd hpos_n (ne_of_lt ha) h_p'_dvd_int,
    cases h_order_is_n',
    exact h_order_is_n'_h,
    exact h_in_factors,
  },
  set ord := order_of (zmod.unit_of_coprime a 
  h_a_coprime_p) with h_ord_def,
  have h_n_eq_ord_mul_pow : ∀ (p' : ℕ) (h_in_factors : p' ∈ Φ.factors),
   ∃ (t : ℕ), n = order_of (zmod.unit_of_coprime a 
  (h_coprime p' (nat.dvd_of_mem_factors h_in_factors))) * p' ^ t ∧ 1 ≤ t,
  {
    intros p' h_in_factors,
    set a_unit := zmod.unit_of_coprime a 
    (h_coprime p' (nat.dvd_of_mem_factors h_in_factors)) with h_a_def,
    have h_root : (polynomial.cyclotomic n (zmod p')).is_root a_unit,
    {
      simp only [zmod.coe_unit_of_coprime, polynomial.is_root.def],
      rw [← polynomial.map_cyclotomic_int, polynomial.eval_nat_cast_map,
      eq_int_cast, zmod.int_coe_zmod_eq_zero_iff_dvd, 
      ← int.to_nat_of_nonneg (polynomial.cyclotomic_nonneg n h_one_le_a_int),
      int.coe_nat_dvd, ← h_Phi_def],
      exact nat.dvd_of_mem_factors h_in_factors,
    },
    have h_p'_prime_fact : fact (p'.prime) := 
    by { rw fact_iff, exact nat.prime_of_mem_factors h_in_factors, },
    cases prime_dvd_cyclotomic hpos_n h_p'_prime_fact h_root with t ht,
    use t,
    split,
    { exact ht, },
    { 
      by_contra,
      simp only [not_le, nat.lt_one_iff] at h,
      subst h,
      simp only [pow_zero, mul_one] at ht,
      have h_order_lt_p' : order_of (zmod.unit_of_coprime a 
      (h_coprime p' (nat.dvd_of_mem_factors h_in_factors))) < p',
      {
        have h_p'_sub_one_lt : p' - 1 < p' := by exact nat.sub_lt 
        (nat.prime.pos (nat.prime_of_mem_factors h_in_factors)) zero_lt_one,
        have h_order_le_p'_sub_one : 
        order_of (zmod.unit_of_coprime a (h_coprime p' 
        (nat.dvd_of_mem_factors h_in_factors))) ≤ p' - 1 := by {
          rw ← nat.totient_prime (nat.prime_of_mem_factors h_in_factors),
          haveI : ne_zero p' := ⟨ nat.prime.ne_zero (nat.prime_of_mem_factors h_in_factors) ⟩, 
          exact order_of_units_le_totient (h_coprime p' 
          (nat.dvd_of_mem_factors h_in_factors)),
        },
        exact lt_of_le_of_lt h_order_le_p'_sub_one h_p'_sub_one_lt,
      },
      apply nat.not_dvd_of_pos_of_lt 
      (order_of_units_pos (h_coprime p' (nat.dvd_of_mem_factors h_in_factors))) h_order_lt_p',
      rw ← ht,
      exact h_p_dvd p' h_in_factors,
    }
  },
  have h_eq_prime_pow : Φ = p ^ Φ.factors.length,
  {
    have h_Phi_pos : Φ ≠ 0 := by linarith,
    apply nat.eq_prime_pow_of_unique_prime_dvd h_Phi_pos,
    intros q h_q_prime h_q_dvd_Phi,
    have h_q_in_factors : q ∈ Φ.factors,
    {
      rw nat.mem_factors,
      split,
      { exact h_q_prime, },
      { exact h_q_dvd_Phi, },
      { linarith, }
    },
    cases h_n_eq_ord_mul_pow p h_p_in_factors with t₁ h_n_eq₁,
    cases h_n_eq₁ with h_n_eq₁ h_one_le_t₁,
    cases h_n_eq_ord_mul_pow q h_q_in_factors with t₂ h_n_eq₂,
    cases h_n_eq₂ with h_n_eq₂ h_one_le_t₂,
    rw h_n_eq₁ at h_n_eq₂,
    have h_p_le_q : p ≤ q := by
    exact le_of_order_mul_pow_eq_order_mul_pow p q t₁ t₂
    h_p_prime h_q_prime
    h_a_coprime_p
    (h_coprime q h_q_dvd_Phi)
    h_one_le_t₁ h_one_le_t₂ h_n_eq₂,
    symmetry' at h_n_eq₂,
    have h_q_le_p : q ≤ p := by
    exact le_of_order_mul_pow_eq_order_mul_pow q p t₂ t₁
    h_q_prime h_p_prime
    (h_coprime q h_q_dvd_Phi)
    h_a_coprime_p
    h_one_le_t₂ h_one_le_t₁ h_n_eq₂,
    exact has_le.le.antisymm h_q_le_p h_p_le_q,
  },
  have h_prime_square_not_dvd : p ^ 2 ∣ Φ → (p = 2 ∧ n = 2),
  {
    intro h_square_dvd,
    have h_Phi_mul_pow_sub_one_dvd : Φ * (a ^ (n / p) - 1) ∣ 
    (a ^ n - 1),
    {
      have h_one_lt_coe_a : 1 < (a : ℤ) := by linarith,
      have h_eq_eval : (a : ℤ) ^ n - 1 = polynomial.eval (a : ℤ) (polynomial.X ^ n - 1) :=
      by simp only [polynomial.eval_sub, polynomial.eval_pow, 
      polynomial.eval_X, polynomial.eval_one],
      have h_eq_eval' : (a : ℤ) ^ (n / p) - 1 = 
      polynomial.eval (a : ℤ) (polynomial.X ^ (n / p) - 1) :=
      by simp only [polynomial.eval_sub, polynomial.eval_pow, 
      polynomial.eval_X, polynomial.eval_one],
      rw [← int.coe_nat_dvd, h_Phi_def, nat.cast_mul, 
      int.coe_nat_sub (one_le_pow_of_one_le (le_of_lt ha) n), 
      int.coe_nat_pow, nat.cast_one,
      int.to_nat_of_nonneg (polynomial.cyclotomic_nonneg n (le_of_lt h_one_lt_coe_a)),
      h_eq_eval, int.coe_nat_sub (one_le_pow_of_one_le (le_of_lt ha) (n / p)), 
      int.coe_nat_pow, nat.cast_one, h_eq_eval', ← polynomial.eval_mul],
      apply polynomial.eval_dvd,
      have h_n_div_p_dvd_n : n / p ∣ n,
      {
        use p,
        symmetry,
        apply nat.div_mul_cancel,
        cases h_n_eq_ord_mul_pow p h_p_in_factors with t ht,
        rw ht.left,
        exact nat_dvd_mul_pow_of_one_le p (order_of (zmod.unit_of_coprime a _)) t ht.right,
      },
      have h_n_div_p_ne_n : n / p ≠ n,
      {
        intro h_eq,
        rw nat.div_eq_self at h_eq,
        cases h_eq,
        { subst h_eq,
        linarith, },
        have h_prime' : prime p := by { rw ← nat.prime_iff, exact h_p_prime },
        { exact prime.ne_one h_prime' h_eq, }
      },
      exact cyclotomic_dvd_X_pow_sub_one_frac ℤ h_n_div_p_dvd_n 
      (nat_ne_zero_of_pos hpos_n) h_n_div_p_ne_n,
    },
    cases h_n_eq_ord_mul_pow p h_p_in_factors with t ht,
    by_contra h_not_exception,
    rw decidable.not_and_distrib at h_not_exception,
    have h_p_dvd_pow_sub_one : (p ∣ a ^ (n / p) - 1) ∧ 
    (p = 2 → 4 ∣ a ^ (n / p) - 1),
    {
      split,
      {
        rw [ht.left, mul_pow_dvd_eq_mul_pow_sub _ p t ht.right],
        exact dvd_pow_order_mul_sub_one _ _ _ _,
      },
      {
        intro h_p_eq_two,
        cases h_not_exception with h_not_p_eq h_not_n_eq,
        {
          exfalso,
          exact h_not_p_eq h_p_eq_two,
        },
        {
          subst h_p_eq_two,
          have h_order_eq_one : order_of (zmod.unit_of_coprime a _) = 1 := 
          by exact order_of_eq_one_in_units_two h_a_coprime_p,
          cases ht with h_n_eq ht,
          rw h_order_eq_one at h_n_eq,
          cases em (1 = t) with h_t_eq_one h_t_ne_one,
          {
            symmetry' at h_t_eq_one,
            subst h_t_eq_one,
            exfalso,
            simp only [pow_one, one_mul] at h_n_eq,
            exact h_not_n_eq h_n_eq,
          },
          {
            have h_two_dvd_n_div : 2 ∣ n / 2,
            {
              use 2 ^ (t - 2),
              rw [h_n_eq, one_mul],
              -- nth_rewrite 1 [← pow_one 2],
              transitivity 2 ^ (t - 1),
              {
                rw ← nat.pow_div ht zero_lt_two,
                rw pow_one,
              },
              {
                rw [← nat.sub_add_cancel 
                (nat_le_sub_one_of_lt 1 t (nat.lt_of_le_and_ne ht h_t_ne_one)),
                nat.sub_sub, one_add_one_eq_two, pow_add, pow_one, mul_comm],
              }
            },
            exact four_dvd_pow_sub_one_of_two_dvd h_a_coprime_p h_two_dvd_n_div,
          }
        }
      }
    },
    have h_multiplicities : 
    multiplicity p Φ + multiplicity p (a ^ (n / p) - 1 ^ (n / p)) ≤ 
    multiplicity p (a ^ n - 1 ^ n),
    {
      rw [← multiplicity.mul 
      (nat.prime.prime (nat.prime_of_mem_factors h_p_in_factors)), one_pow, one_pow],
      exact multiplicity.multiplicity_le_multiplicity_of_dvd_right 
      h_Phi_mul_pow_sub_one_dvd,
    },
    have h_multiplicities' :
    multiplicity (p : ℤ) (Φ : ℤ) + 
    multiplicity (p : ℤ) ((a : ℤ) ^ (n / p) - 1 ^ (n / p)) ≤ 
    multiplicity (p : ℤ) ((a : ℤ) ^ n - 1 ^ n),
    {
      rw [one_pow, one_pow] at h_multiplicities,
      rw [one_pow, one_pow, ← nat.cast_one, ← int.coe_nat_pow,
      ← int.coe_nat_pow,
      ← int.coe_nat_sub (h_one_le (n / p)),
      ← int.coe_nat_sub (h_one_le n)],
      repeat { rw multiplicity.int.coe_nat_multiplicity, },
      exact h_multiplicities,
    },
    have h_p_dvd_n : p ∣ n,
    {
      rw ht.left,
      exact nat_dvd_mul_pow_of_one_le p 
      (order_of (zmod.unit_of_coprime a _)) t ht.right,
    },
    nth_rewrite 2 ← nat.div_mul_cancel h_p_dvd_n at h_multiplicities',
    nth_rewrite 3 ← nat.div_mul_cancel h_p_dvd_n at h_multiplicities',
    rw [pow_mul, pow_mul] at h_multiplicities',
    have h_p_not_dvd_a_pow : ¬(p : ℤ) ∣ (a : ℤ) ^ (n / p),
    {
      intro h_p_dvd_pow,
      have h_p_coprime_a : (p : ℕ).coprime a := 
      by { exact nat.coprime.symm h_a_coprime_p },
      rw nat.prime.coprime_iff_not_dvd h_p_prime at h_p_coprime_a,
      apply h_p_coprime_a,
      rw ← int.coe_nat_dvd,
      exact int.prime.dvd_pow' h_p_prime h_p_dvd_pow,
    },
    cases nat.prime.eq_two_or_odd' h_p_prime with h_p_eq_two h_p_odd,
    {
      subst h_p_eq_two,
      have h_four_dvd : 4 ∣ (a : ℤ) ^ (n / 2) - 1 ^ (n / 2),
      {
        rw [one_pow, ← nat.cast_one, ← int.coe_nat_pow,
        ← int.coe_nat_sub (h_one_le (n / 2)), ← coe_bit0, ← coe_bit0,
        int.coe_nat_dvd],
        apply h_p_dvd_pow_sub_one.right,
        refl,
      },
      rw [nat.cast_two, 
      int.two_pow_sub_pow' 2 h_four_dvd _, add_comm] at h_multiplicities',
      nth_rewrite 7 ← nat.cast_two at h_multiplicities',
      rw [multiplicity.int.coe_nat_multiplicity, 
      nat_multiplicity_self 2 (le_refl 2)] at h_multiplicities',
      rw [multiplicity.pow_dvd_iff_le_multiplicity,
      ← multiplicity.int.coe_nat_multiplicity, nat.cast_two,
      nat.cast_two] at h_square_dvd,
      -- apply not_lt_of_le (le_of_add_le_add_left h_multiplicities'),
      sorry,
      {
        rw nat.cast_two at h_p_not_dvd_a_pow,
        exact h_p_not_dvd_a_pow,
      }
    },
    {
      have h_p_dvd_pow_sub_pow : (p : ℤ) ∣ (a : ℤ) ^ (n / p) - 1 ^ (n / p),
      {
        rw [one_pow, ← nat.cast_one, ← int.coe_nat_pow,
        ← int.coe_nat_sub (h_one_le (n / p)), int.coe_nat_dvd],
        exact h_p_dvd_pow_sub_one.left,
      },
      rw [multiplicity.int.pow_sub_pow h_p_prime h_p_odd 
      h_p_dvd_pow_sub_pow h_p_not_dvd_a_pow p,
      nat_multiplicity_self p (nat.prime.two_le h_p_prime), add_comm]
      at h_multiplicities',
      rw [multiplicity.pow_dvd_iff_le_multiplicity,
      ← multiplicity.int.coe_nat_multiplicity] at h_square_dvd,
      sorry,
    }
  },
  cases em (p = 2 ∧ n = 2) with h_exception h_not_exception_1,
  {
    cases h_exception,
    subst h_exception_right,
    subst h_exception_left,
    simp only [polynomial.cyclotomic_two, polynomial.eval_add, 
    polynomial.eval_X, polynomial.eval_one, 
    int.to_nat_coe_nat_add_one] at h_Phi_def,
    apply h_exception_1,
    split,
    { refl, },
    {
      use Φ.factors.length,
      rw h_eq_prime_pow at h_Phi_def,
      rw h_Phi_def,
      simp only [nat.add_succ_sub_one, add_zero],
    }
  },
  {
    have h_square_not_dvd : ¬ p ^ 2 ∣ Φ := 
    by { intro h_dvd, exact h_not_exception_1 (h_prime_square_not_dvd h_dvd), },
    have h_factors_length_eq_one : Φ.factors.length = 1,
    {
      cases others with p' others' h_primes',
      {
        rw [h_primes, list.length_singleton],
      },
      {
        exfalso,
        apply h_square_not_dvd,
        rw h_eq_prime_pow, 
        apply pow_dvd_pow p,
        rw h_primes,
        simp only [list.length],
        rw [add_assoc, one_add_one_eq_two],
        exact nat.le_add_left 2 others'.length,
      }
    },
    rw [h_factors_length_eq_one, pow_one, h_Phi_def,
    ← int.coe_nat_eq_coe_nat_iff, int.to_nat_of_nonneg 
    (polynomial.cyclotomic_nonneg n h_one_le_a_int)] at h_eq_prime_pow,
    cases h_n_eq_ord_mul_pow p h_p_in_factors with t ht,
    rw [mul_comm, ← h_ord_def] at ht,
    rw ht.left at h_eq_prime_pow,
    have h_p_not_dvd_ord : ¬ p ∣ ord,
    {
      rw h_ord_def,
      apply nat.not_dvd_of_pos_of_lt (order_of_units_pos _),
      haveI : ne_zero p := ⟨ nat.prime.ne_zero h_p_prime ⟩,
      have h_ord_le_p_sub_one : order_of (zmod.unit_of_coprime a _) ≤ p - 1 := 
      by { rw ← nat.totient_prime h_p_prime, 
      exact order_of_units_le_totient h_a_coprime_p, },
      have h_p_sub_one_lt_p : p - 1 < p,
      {
        rw ← nat.sub_zero (p - 1),
        exact nat.sub_one_sub_lt (nat.prime.pos h_p_prime),
      },
      exact lt_of_le_of_lt h_ord_le_p_sub_one h_p_sub_one_lt_p,
    },
    have h_expand_eq_expand_mul_p : 
    polynomial.eval ↑a ((polynomial.expand ℤ (p ^ t)) 
    (polynomial.cyclotomic ord ℤ)) =
    polynomial.eval ↑a ((polynomial.expand ℤ (p ^ (t - 1))) 
    (polynomial.cyclotomic ord ℤ)) * ↑p,
    {
      rw [cyclotomic_expand_pow_eq_cyclotomic_mul h_p_prime _ h_p_not_dvd_ord,
      polynomial.eval_mul, h_eq_prime_pow, mul_comm],
      linarith,
    },
    simp only [polynomial.expand_eval] at h_expand_eq_expand_mul_p,
    apply eq.not_gt h_expand_eq_expand_mul_p,
    cases em (ord = 1) with h_ord_eq_one h_ord_ne_one,
    {
      simp only [h_ord_eq_one, polynomial.cyclotomic_one, 
      polynomial.eval_sub, polynomial.eval_X, 
      polynomial.eval_one],
      nth_rewrite 1 ← nat.sub_add_cancel ht.right,
      nth_rewrite 1 ← nat.cast_one,
      nth_rewrite 4 ← nat.cast_one,
      rw [← int.coe_nat_pow,
      ← int.coe_nat_pow,
      ← int.coe_nat_sub (h_one_le (p ^ (t - 1))),
      ← int.coe_nat_sub (h_one_le (p ^ (t - 1 + 1))), pow_add,
      pow_mul, pow_one, ← int.coe_nat_mul, int.coe_nat_lt],
      apply sub_one_mul_lt_pow_sub_one (a ^ p ^ (t - 1)) p,
      apply h_one_lt (p ^ (t - 1)),
      exact pow_pos (nat.prime.pos h_p_prime) (t - 1),
    },
    {
      have h_ord_pos : 0 < ord := by { rw h_ord_def, 
      exact order_of_units_pos h_a_coprime_p, },
      have h_one_lt_ord : 1 < ord,
      {
        rw nat.one_lt_iff_ne_zero_and_ne_one,
        split,
        { exact nat_ne_zero_of_pos h_ord_pos, },
        { exact h_ord_ne_one, }
      },
      have h_le : ((a : ℤ) ^ p ^ (t - 1) + 1) ^ ord.totient * ↑p ≤ 
      ((a : ℤ) ^ p ^ t - 1) ^ ord.totient,
      {
        nth_rewrite 1 ← nat.sub_add_cancel ht.right,
        set b := (a : ℤ) ^ p ^ (t - 1) with h_b_def,
        rw [pow_add, pow_mul, pow_one, ← h_b_def],
        sorry,
      },
      exact lt_of_le_of_lt 
      (le_trans (int.mul_le_mul_of_nonneg_right (cyclotomic_le_X_add_one_pow h_ord_pos 
      (h_one_lt_int (p ^ (t - 1)) 
      (pow_pos (nat.prime.pos h_p_prime) (t - 1)))) (int.coe_nat_nonneg p)) h_le)
      (X_sub_one_pow_lt_cyclotomic h_one_lt_ord 
      (h_one_lt_int (p ^ t) (pow_pos (nat.prime.pos h_p_prime) t))),
    }
  }
end

lemma h_le (a p t ord n : ℕ) (ht: n = p ^ t * ord ∧ 1 ≤ t)
(h_one_lt_ord : 1 < ord) (h_ord_pos : 0 < ord) (ha: 1 < a) (h_p_prime : nat.prime p)
(h_exception_2 : ¬(n = 6 ∧ a = 2)) (h_a_coprime_p: a.coprime p)
(h_ord_def: ord = order_of (zmod.unit_of_coprime a h_a_coprime_p))
: ((a : ℤ) ^ p ^ (t - 1) + 1) ^ ord.totient * ↑p ≤ 
((a : ℤ) ^ p ^ t - 1) ^ ord.totient := 
begin
  nth_rewrite 1 ← nat.sub_add_cancel ht.right,
  set b := (a : ℤ) ^ p ^ (t - 1) with h_b_def,
  rw [pow_add, pow_mul, pow_one, ← h_b_def],
  have h_b_nonneg : 0 ≤ b,
  {
    rw h_b_def,
    apply pow_nonneg,
    linarith,
  },
  transitivity ((b + 1) * ↑p) ^ ord.totient,
  {
    rw mul_pow,
    apply int.mul_le_mul_of_nonneg_left,
    {
      apply le_self_pow _ (nat_ne_zero_of_pos (nat.totient_pos h_ord_pos)),
      rw [← nat.cast_one, int.coe_nat_le],
      exact le_of_lt (nat.prime.one_lt h_p_prime),
    },
    {
      apply pow_nonneg,
      apply add_nonneg h_b_nonneg,
      linarith,
    }
  },
  {
    apply pow_le_pow_of_le_left,
    {
      apply mul_nonneg,
      {
        apply add_nonneg h_b_nonneg,
        linarith,
      },
      {
        linarith,
      }
    },
    {
      cases em (b ≤ 2) with h_b_le_two h_two_lt_b,
      {
        have h_pow_le_two : 2 ^ (p ^ (t - 1)) ≤ (2 : ℤ),
        {
          transitivity (↑a ^ p ^ (t - 1)),
          {
            apply pow_le_pow_of_le_left,
            { linarith, },
            {
              rw [← nat.cast_two, int.coe_nat_le],
              linarith,
            }
          },
          {
            rw ← h_b_def,
            exact h_b_le_two,
          }
        },
        nth_rewrite 1 ← pow_one (2 : ℤ) at h_pow_le_two,
        rw [pow_le_pow_iff _] at h_pow_le_two,
        {
          cases em (t - 1 = 0) with h_t_le_one h_t_ne_one,
          {
            rw nat.sub_eq_zero_iff_le at h_t_le_one,
            have h_t_eq_one : t = 1 := by exact le_antisymm h_t_le_one ht.right,
            subst h_t_eq_one,
            simp only [pow_zero, pow_one] at h_b_def,
            rw [h_b_def, ← nat.cast_two, int.coe_nat_le] at h_b_le_two,
            have h_a_eq_two : a = 2 := by linarith,
            subst h_a_eq_two,
            have h_p_ne_two : p ≠ 2,
            {
              intro h_p_eq_two,
              rw [h_p_eq_two, nat.coprime_self] at h_a_coprime_p,
              linarith,
            },
            cases em (p = 3) with h_p_eq_three h_p_ne_three,
            {
              subst h_p_eq_three,
              exfalso,
              apply h_exception_2,
              rw [eq_self_iff_true, and_true, ht.left, pow_one, 
              h_ord_def, order_of_two_mod_three_eq_two h_a_coprime_p],
              ring,
            },
            {
              rw [h_b_def, coe_bit0, algebra_map.coe_one],
              have h_five_le_p : 5 ≤ p := by exact 
              nat.prime.five_le_of_ne_two_of_ne_three h_p_prime h_p_ne_two h_p_ne_three,
              
              sorry,
            }
          },
          {
            exfalso,
            rw nat_pow_le_one_iff at h_pow_le_two,
            cases h_pow_le_two,
            { exact not_lt_of_le h_pow_le_two (nat.prime.one_lt h_p_prime), },
            { exact h_t_ne_one h_pow_le_two, }
          }
        },
        {
          linarith,
        }
      },
      {

        transitivity 2 * (b - 1) * ↑p,
        {
          apply int.mul_le_mul_of_nonneg_right,
          { linarith, },
          { linarith, }
        },
        {
          rw ← mul_geom_sum b p,
          sorry,
        }
      }
    }
  }
end