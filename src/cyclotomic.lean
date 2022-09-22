import ring_theory.polynomial.cyclotomic.basic
import algebra
import data.set
import tactic

variables {R : Ring} {n : ℕ} {a : R}

def pow' {R : Ring} (n : ℕ) (a : R) := pow a n

def polynomial_value (p : polynomial R) := p.sum pow'

noncomputable theory

lemma nat_ne_zero_of_pos {n : ℕ} : 0 < n → n ≠ 0 :=
begin
  intros h1 h2,
  subst h2,
  simp at h1,
  exact h1, 
end

lemma unit_of_coprime_of_val {n : ℕ} [ne_zero n] (a : (zmod n)ˣ) : 
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
{n k : ℕ} (hdvd : k ∣ n) (hposn : n ≠ 0) (hposk : k ≠ 0) (hne : k ≠ n) : 
polynomial.cyclotomic n R * (polynomial.X ^ k - 1) ∣ polynomial.X ^ n - 1 :=
begin
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
      exact cyclotomic_dvd_X_pow_sub_one_frac _ hdvd_mn (nat_ne_zero_of_pos hpos) 
      (nat_ne_zero_of_pos h_m_pos) h_ne_mn,
    },
    cases h_dvd_cyclotomic with P h_dvd_polynoms,
    rw h_dvd_polynoms,
    simp at hroot ⊢,
    left,
    exact hroot,
  } 
end