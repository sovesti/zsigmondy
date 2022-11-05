import ring_theory.polynomial.cyclotomic.basic
import ring_theory.polynomial.cyclotomic.eval
import algebra
import data.finset
import tactic

variables {R : Ring} {n : ℕ} {a : R}

noncomputable theory

lemma nat_ne_zero_of_pos {n : ℕ} : 0 < n → n ≠ 0 :=
begin
  intros h1 h2,
  subst h2,
  simp at h1,
  exact h1, 
end

lemma unit_of_coprime_of_val [ne_zero n] (a : (zmod n)ˣ) : 
zmod.unit_of_coprime (a : zmod n).val (zmod.val_coe_unit_coprime _) = a :=
begin
  rw ← units.eq_iff,
  simp,
end

lemma polynomial_dvd_of_mul_dvd_mul {R : Type u_1} [field R] {p q r : polynomial R} 
(hr : r ≠ 0) : p * r ∣ q * r → p ∣ q :=
begin
  intro hdvd,
  cases hdvd with t hdvd,
  use t,
  have h_qr_eq_ptr : q * r = p * t * r := by simp [hdvd, mul_comm, mul_assoc],
  rw mul_eq_mul_right_iff at h_qr_eq_ptr,
  cases h_qr_eq_ptr,
  { exact h_qr_eq_ptr, },
  {
    exfalso,
    exact hr h_qr_eq_ptr,
  }
end

theorem cyclotomic_dvd_X_pow_sub_one_frac (R : Type u_1) [comm_ring R] [is_domain R] 
{k : ℕ} (hdvd : k ∣ n) (hposn : n ≠ 0) (hne : k ≠ n) : 
polynomial.cyclotomic n R * (polynomial.X ^ k - 1) ∣ polynomial.X ^ n - 1 :=
begin
  cases em (k = 0) with h_k_zero hposk,
  {
    subst h_k_zero,
    rw zero_dvd_iff at hdvd,
    exfalso,
    exact hposn hdvd,
  },
  rw [← polynomial.prod_cyclotomic_eq_X_pow_sub_one (nat.pos_of_ne_zero hposk), 
  ← polynomial.prod_cyclotomic_eq_X_pow_sub_one (nat.pos_of_ne_zero hposn)],
  have h_subset : k.divisors ⊆ n.divisors,
  { exact nat.divisors_subset_of_dvd hposn hdvd, },
  have h_in_n_divisors : n ∈ n.divisors,
  { simp [hposn], },
  have h_not_in_k_divisors : n ∉ k.divisors,
  { 
    intro h_in_divisors,
    apply hne,
    apply le_antisymm,
    { exact nat.le_of_dvd (nat.pos_of_ne_zero hposn) hdvd, },
    { exact nat.divisor_le h_in_divisors, }
  },
  use (n.divisors.erase n \ k.divisors).prod (λ (i : ℕ), polynomial.cyclotomic i R),
  rw [mul_assoc, ← finset.prod_union, finset.union_comm, 
  finset.sdiff_union_of_subset, mul_comm, finset.prod_erase_mul],
  exact h_in_n_divisors,
  {
    rw finset.subset_erase,
    split,
    { exact h_subset, },
    { exact h_not_in_k_divisors }
  },
  {
    rw disjoint.comm,
    exact finset.sdiff_disjoint,
  }
end

theorem prime_dvd_cyclotomic (hpos : 0 < n) 
{p : ℕ} [hprime : fact (nat.prime p)] {a : (zmod p)ˣ}
(hroot : (polynomial.cyclotomic n (zmod p)).is_root a) : 
∃ (t : ℕ), n = order_of a * p ^ t :=
begin
  let a' : ℕ := (a : zmod p).val,
  have hroot' : (polynomial.cyclotomic n (zmod p)).is_root a',
  {
    rw zmod.nat_cast_zmod_val,
    exact hroot,
  },
  have hdvd : ∃ (k : ℕ), n = order_of a * k,
  {
    cases polynomial.order_of_root_cyclotomic_dvd hpos hroot' with l hdvd,
    use l,
    rw hdvd,
    simp,
    left,
    rw unit_of_coprime_of_val,
  },
  cases hdvd with k,
  rw hdvd_h,
  use k.factors.length,
  simp,
  left,
  apply nat.eq_prime_pow_of_unique_prime_dvd,
  {
    cases k,
    {
      rw hdvd_h at hpos,
      simp at hpos,
      exfalso,
      exact hpos,
    },
    { simp, }
  },
  {
    intros q h_q_prime hdvd,
    have hdvd_qn : q ∣ n,
    {
      cases hdvd with l h,
      use order_of a * l,
      simp [h, hdvd_h],
      linarith,
    },
    cases hdvd_qn with m h_qm_eq_n,
    by_contra,
    have h_ndvd : 
    ¬ ((finset.range q).sum (λ (i : ℕ), (polynomial.X ^ m) ^ i)).is_root a.val,
    {
      simp,
      intro h_root_of_sum,
      rw polynomial.eval_finset_sum at h_root_of_sum, 
      simp at h_root_of_sum,
      have h_dvd_order : ∀ (i : ℕ), order_of a ∣ m * i,
      {
        cases hdvd with t hdvd_t,
        intro i,
        use t * i,
        subst hdvd_h,
        subst hdvd_t,
        rw [mul_comm, mul_assoc, nat.mul_right_inj] at h_qm_eq_n,
        rw ← h_qm_eq_n,
        linarith,
        { exact nat.pos_of_ne_zero (nat.prime.ne_zero h_q_prime), }
      },

      repeat { simp_rw ← units.coe_pow _ _ at h_root_of_sum, },
      simp_rw ← pow_mul at h_root_of_sum,
      simp_rw order_of_dvd_iff_pow_eq_one at h_dvd_order,
      simp_rw h_dvd_order at h_root_of_sum,
      rw finset.sum_const at h_root_of_sum,
      rw finset.card_range at h_root_of_sum,
      dsimp at h_root_of_sum,
      simp at h_root_of_sum,
      rw [zmod.nat_coe_zmod_eq_zero_iff_dvd, 
      nat.prime.dvd_iff_eq h_q_prime (nat.prime.ne_one hprime.out)] at h_root_of_sum,
      exact h h_root_of_sum,
    },
    apply h_ndvd,
    have h_dvd_cyclotomic : polynomial.cyclotomic n (zmod p) ∣ 
    (finset.range q).sum (λ (i : ℕ), (polynomial.X ^ m) ^ i),
    {
      have h_m_pos : 0 < m,
      {
        apply nat.pos_of_ne_zero,
        intro h_m_is_zero,
        rw h_m_is_zero at h_qm_eq_n,
        subst h_qm_eq_n,
        simp at hpos,
        exact hpos,
      },
      apply polynomial_dvd_of_mul_dvd_mul (polynomial.X_pow_sub_C_ne_zero h_m_pos (1 : zmod p)),
      rw mul_comm at h_qm_eq_n,
      rw [polynomial.C_1, geom_sum_mul _ q, ← pow_mul, ← h_qm_eq_n],
      have hdvd_mn : m ∣ n,
      {
        use q,
        exact h_qm_eq_n,
      },
      have h_ne_mn : m ≠ n,
      {
        intro h_eq_mn,
        rw h_eq_mn at h_qm_eq_n,
        apply nat.prime.ne_one h_q_prime,
        rw ← nat.mul_right_eq_self_iff hpos,
        symmetry,
        exact h_qm_eq_n,
      },
      exact cyclotomic_dvd_X_pow_sub_one_frac _ hdvd_mn (nat_ne_zero_of_pos hpos) h_ne_mn,
    },
    cases h_dvd_cyclotomic with P h_dvd_polynoms,
    rw h_dvd_polynoms,
    simp at hroot ⊢,
    left,
    exact hroot,
  } 
end

lemma cyclotomic_eval_int_eq_eval_real {a : ℤ} :
↑(polynomial.eval (a : ℤ) (polynomial.cyclotomic n ℤ)) = 
        polynomial.eval (a : ℝ) (polynomial.cyclotomic n ℝ) :=
begin
  simp only [← polynomial.map_cyclotomic_int n ℝ, polynomial.eval_int_cast_map,
          int.cast_id, eq_int_cast],
end

theorem cyclotomic_le_X_add_one_pow {a : ℤ} (hposn : 0 < n) (ha : 1 < a) : 
polynomial.eval a (polynomial.cyclotomic n ℤ) ≤ (a + 1) ^ (n.totient) :=
begin
  cases em (n = 1) with n_is_one n_ne_one,
  {
    unfreezingI { subst n_is_one, },
    simp only [polynomial.cyclotomic_one, polynomial.eval_sub, polynomial.eval_X, 
    polynomial.eval_one, nat.totient_one, pow_one, tsub_le_iff_right],
    linarith,
  },
  {
    cases em (n = 2) with n_is_two n_ne_two,
    {
      unfreezingI { subst n_is_two, },
      simp only [polynomial.cyclotomic_two, polynomial.eval_add, polynomial.eval_X, 
      polynomial.eval_one, nat.totient_two, pow_one],
    },
    {
      have hn : 3 ≤ n,
      {
        rw nat.add_one_le_iff,
        exact nat.two_lt_of_ne (nat_ne_zero_of_pos hposn) n_ne_one n_ne_two,
      },
      have ha' :  1 < (a : ℝ),
      {
        rw [← int.cast_one, int.cast_lt],
        exact ha,
      },
      have h_le_in_R : ↑(polynomial.eval (a : ℤ) (polynomial.cyclotomic n ℤ)) ≤ 
      ((a + 1) ^ (n.totient) : ℝ),
      {
        rw cyclotomic_eval_int_eq_eval_real,
        apply le_of_lt,
        exact polynomial.cyclotomic_eval_lt_sub_one_pow_totient hn ha',
      },
      rw [← int.cast_one, ← int.cast_add, ← int.cast_pow, int.cast_le] at h_le_in_R,
      exact h_le_in_R,
    }
  }
end

theorem X_sub_one_pow_le_cyclotomic {a : ℤ} (hposn : 1 < n) (ha : 1 < a) : 
(a - 1) ^ (n.totient) < polynomial.eval a (polynomial.cyclotomic n ℤ) :=
begin
  cases em (n = 1) with n_is_one n_ne_one,
  {
    unfreezingI { subst n_is_one, },
    linarith,
  },
  {
    cases em (n = 2) with n_is_two n_ne_two,
    {
      unfreezingI { subst n_is_two, },
      simp only [polynomial.cyclotomic_two, polynomial.eval_add, polynomial.eval_X, 
      polynomial.eval_one, nat.totient_two, pow_one],
      linarith,
    },
    {
      have hn : 2 ≤ n,
      {
        rw [nat.add_one_le_iff, nat.one_lt_iff_ne_zero_and_ne_one],
        split,
        {
          intro h,
          subst h,
          linarith,
        },
        exact n_ne_one,
      },
      have ha' :  1 < (a : ℝ),
      {
        rw [← int.cast_one, int.cast_lt],
        exact ha,
      },
      have h_le_in_R : ((a - 1) ^ (n.totient) : ℝ) < 
      ↑(polynomial.eval (a : ℤ) (polynomial.cyclotomic n ℤ)),
      {
        rw cyclotomic_eval_int_eq_eval_real,
        exact polynomial.sub_one_pow_totient_lt_cyclotomic_eval hn ha',
      },
      rw [← int.cast_one, ← int.cast_sub, ← int.cast_pow, int.cast_lt] at h_le_in_R,
      exact h_le_in_R,
    }
  }
end

theorem cyclotomic_expand_pow_eq_cyclotomic_mul
{p t m : ℕ} [hprime : nat.prime p] 
(hpost : 0 < t) (h_not_dvd : ¬p ∣ m) :
(polynomial.expand ℤ (p ^ t)) (polynomial.cyclotomic m ℤ) =
(polynomial.cyclotomic (p ^ t * m) ℤ) * 
(polynomial.expand ℤ (p ^ (t - 1)) (polynomial.cyclotomic m ℤ)) :=
begin
  induction t with t ht,
  {
    exfalso,
    exact nat.not_lt_zero 0 hpost,
  },
  {
    cases em (t = 0) with h_t_eq_zero h_t_ne_zero,
    {
      subst h_t_eq_zero,
      simp only [pow_one, pow_zero, polynomial.expand_one, mul_comm p m,
      polynomial.cyclotomic_expand_eq_cyclotomic_mul hprime h_not_dvd],
    },
    {
      have h_pow : p * p ^ (t - 1) = p ^ t,
      {
        rw [← ne.def, ← nat.one_le_iff_ne_zero] at h_t_ne_zero,
        rw [← nat.sub_add_cancel h_t_ne_zero, pow_add, mul_comm],
        simp only [nat.add_succ_sub_one, add_zero, pow_one],
      },
      simp only [nat.succ_eq_add_one, nat.succ_sub_succ_eq_sub, tsub_zero, pow_add, pow_one],
      have h_expand : (polynomial.expand ℤ (p ^ t)) (polynomial.cyclotomic m ℤ) = 
      (polynomial.expand ℤ p) ((polynomial.expand ℤ (p ^ (t - 1))) (polynomial.cyclotomic m ℤ)),
      { rw [← polynomial.expand_mul, h_pow], },
      rw [mul_comm, polynomial.expand_mul, mul_comm p _, mul_assoc, mul_comm p _,
      ← mul_assoc, ← polynomial.cyclotomic_expand_eq_cyclotomic hprime, h_expand,
      ← alg_hom.map_mul, polynomial.expand_inj (nat.prime.pos hprime), ← h_expand],
      exact ht (nat.pos_of_ne_zero h_t_ne_zero),
      {
        use p ^ (t - 1) * m,
        rw [← mul_assoc, h_pow],
      }
    }
  }
end

theorem order_of_eq_iff_is_root_of_cyclotomic {a p : ℕ} (h_prime : fact p.prime)
(h_ndvd : ¬ p ∣ n) (h_pos : 0 < n) (h_a : 1 ≠ a) :
↑p ∣ (polynomial.cyclotomic n ℤ).eval ↑a → ∃ (h_coprime : a.coprime p),
order_of(zmod.unit_of_coprime a h_coprime) = n :=
begin 
  intro hdvd,
  have h_coprime: a.coprime p,
  {
    rw ← zmod.int_coe_zmod_eq_zero_iff_dvd at hdvd,
    apply polynomial.coprime_of_root_cyclotomic h_pos,
    rw [polynomial.is_root.def, ← polynomial.map_cyclotomic_int, eq_nat_cast,
    polynomial.eval_nat_cast_map, eq_int_cast],
    exact hdvd,
  },
  use h_coprime,
  have h_one_le : ∀ (k : ℕ), 1 ≤ a ^ k,
  { 
    intro k,
    apply nat.one_le_pow,
    apply nat.pos_of_ne_zero,
    intro h,
    subst h,
    rw nat.coprime_zero_left at h_coprime,
    exact nat.prime.ne_one h_prime.out h_coprime,
  },
  have h_one_ne : ∀ (k : ℕ) (h_ne_zero : k ≠ 0), 1 ≠ a ^ k,
  {
    intros k h_ne_zero h,
    apply h_a,
    cases k,
    { exfalso, apply h_ne_zero, refl, },
    rw [nat.succ_eq_add_one, pow_add] at h,
    symmetry' at h,
    rw [nat.mul_eq_one_iff, pow_one] at h,
    symmetry,
    exact h.2,
  },
  have h_one_ne' : ∀ (k : ℕ) (h_ne_zero : k ≠ 0), a ^ k - 1 ≠ 0,
  {
    intros k h_ne_zero h,
    rw [nat.sub_eq_zero_iff_le] at h,
    apply h_one_ne k h_ne_zero,
    exact le_antisymm (h_one_le k) h,
  },
  have h_one_ne_int : ∀ (k : ℕ) (h_ne_zero : k ≠ 0), (a : ℤ)^k - 1 ≠ 0,
  {
    intros k h_ne_zero h,
    apply h_one_ne' k h_ne_zero,
    rw [← int.coe_nat_eq_coe_nat_iff, int.coe_nat_zero,
     int.coe_nat_sub (h_one_le k), int.coe_nat_pow, int.coe_nat_one],
    exact h,
  },
  have hdvd' : ∀ (d : ℕ) (h_dvdn : d ∣ n) (hd : d ≠ n), p * (a ^ d - 1) ∣ (a ^ n - 1),
  {
    intros d h_dvdn hd,
    suffices h_dvd_eval : ↑p * polynomial.eval (a : ℤ) (polynomial.X ^ d - 1) 
    ∣ polynomial.eval (a : ℤ) (polynomial.X ^ n - 1),
    {
      simp only [eq_int_cast, int.cast_one, polynomial.eval_sub, 
      polynomial.eval_pow, polynomial.eval_X, polynomial.eval_one] at h_dvd_eval,
      rw [← int.coe_nat_dvd, nat.cast_mul],
      rw [int.coe_nat_sub (h_one_le d), int.coe_nat_sub (h_one_le n),
      int.coe_nat_pow, nat.cast_one, int.coe_nat_pow],
      exact h_dvd_eval,
    },
    {
      transitivity polynomial.eval ↑a (polynomial.cyclotomic n ℤ) * 
      (polynomial.eval ↑a (polynomial.X ^ d - 1)),
      { exact mul_dvd_mul_right hdvd _, },
      {
        rw ← polynomial.eval_mul, 
        apply polynomial.eval_dvd,
        exact cyclotomic_dvd_X_pow_sub_one_frac ℤ h_dvdn (nat_ne_zero_of_pos h_pos) hd,
      }
    }
  },
  have h_order_dvd_n : order_of (zmod.unit_of_coprime a h_coprime) ∣ n,
  {
    apply order_of_dvd_of_pow_eq_one,
    rw [← units.eq_iff, ← sub_eq_zero, units.coe_pow,
    zmod.coe_unit_of_coprime, units.coe_one, ← nat.cast_one, ← nat.cast_pow,
    ← nat.cast_sub (h_one_le n), ← int.cast_coe_nat, zmod.int_coe_zmod_eq_zero_iff_dvd,
    int.coe_nat_dvd],
    cases em (1 = n),
    {
      symmetry' at h,
      subst h,
      simp only [polynomial.cyclotomic_one, polynomial.eval_sub, 
      polynomial.eval_X, polynomial.eval_one] at hdvd,
      rw [← int.coe_nat_dvd, nat.cast_sub (h_one_le 1), pow_one, nat.cast_one],
      exact hdvd,
    },
    exact dvd_of_mul_right_dvd (hdvd' 1 (one_dvd n) h),
  },
  by_contra,
  let ord := order_of (zmod.unit_of_coprime a h_coprime),
  have ord_def : order_of (zmod.unit_of_coprime a h_coprime) = ord := by refl,
  have h_ord_pos : ord ≠ 0,
  {
    intro h_zero,
    rw [← ord_def, order_of_eq_zero_iff] at h_zero,
    apply h_zero,
    rw is_of_fin_order_iff_pow_eq_one,
    use fintype.card((zmod p)ˣ),
    split,
    { exact fintype.card_pos, },
    { rw pow_card_eq_one, }
  },
  have hdvd'' : p * (a ^ ord - 1) ∣ a ^ n - 1,
  { exact hdvd' ord h_order_dvd_n h, },
  rw ord_def at h_order_dvd_n,
  cases h_order_dvd_n with t h_mul,
  subst h_mul,
  rw [← int.coe_nat_dvd, nat.cast_mul, 
  nat.cast_sub (h_one_le ord), nat.cast_sub (h_one_le (ord * t))] at hdvd'',
  simp only [int.coe_nat_pow, nat.cast_one] at hdvd'',
  rw [pow_mul, ← geom_sum_mul (↑a ^ ord) t] at hdvd'',
  have hdvd''' : (p : ℤ) ∣ (finset.range t).sum (λ (i : ℕ), (↑a ^ ord) ^ i),
  {
    exact int.dvd_of_mul_dvd_mul_right (h_one_ne_int ord h_ord_pos) hdvd'',
  },
  simp only [← zmod.int_coe_zmod_eq_zero_iff_dvd, 
  int.cast_sum, int.cast_pow, int.cast_coe_nat, ← ord_def,
  ← zmod.coe_unit_of_coprime a h_coprime, ← units.coe_pow,
  pow_order_of_eq_one, units.coe_one, one_pow, finset.sum_const, 
  finset.card_range, nat.smul_one_eq_coe] at hdvd''',
  rw zmod.nat_coe_zmod_eq_zero_iff_dvd at hdvd''',
  rw mul_comm at h_ndvd,
  exact h_ndvd (dvd_mul_of_dvd_left hdvd''' ord),
end