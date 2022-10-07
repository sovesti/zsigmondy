import ring_theory.polynomial.cyclotomic.basic
import algebra
import data.finset
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

lemma finset_bij {n : ℕ}   : 
((finset.Ioc 0 (n / 2)).filter (λ (i : ℕ), i.coprime n)).prod 
            (λ (x : ℕ), polynomial.X - 
            polynomial.C (complex.exp (2 * ↑real.pi * ((↑n - ↑x) / ↑n) * complex.I))) =
            ((finset.Ioc (n / 2) n).filter (λ (i : ℕ), i.coprime n)).prod 
            (λ (x : ℕ), polynomial.X - 
            polynomial.C (complex.exp (2 * ↑real.pi * (↑x / ↑n) * complex.I)))
            :=
begin
  apply finset.prod_bij' (λ i h, n - i) _ _ (λ i h, n - i) _,
  {
    intros a ha,
    dsimp,
    simp only [finset.mem_filter, finset.mem_Ioc] at ha,
    apply nat.sub_sub_self,
    exact ha.1.2.trans (nat.div_le_self n 2),
  },
  all_goals { sorry, }
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

theorem cyclotomic_le_X_sub_one_pow {n : ℕ} {a : ℤ} [fintype (zmod n)ˣ] 
(hposn : 0 < n) (hposa : 0 < a) : 
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
      have cyclotomic_eq_prod : polynomial.map (int.cast_ring_hom ℝ) (polynomial.cyclotomic n ℤ) = 
      finset.prod (finset.filter (λ (i : ℕ), i.coprime n) (finset.range (n / 2))) (λ (i : ℕ), polynomial.X ^ 2 
      - (polynomial.C (2 * (complex.exp (2 * ↑real.pi * (↑i / ↑n) * complex.I)).re)) * polynomial.X + 
      polynomial.C 1),
      {
        apply polynomial.map_injective complex.of_real _,
        {
          transitivity polynomial.map (int.cast_ring_hom ℂ) (polynomial.cyclotomic n ℤ),
          {
            simp only [polynomial.map_cyclotomic],
          },
          {
            rw (polynomial.int_cyclotomic_spec n).1,
            rw polynomial.map_prod,
            simp only [coe_coe, map_mul, polynomial.C_bit0, map_one, polynomial.map_add, 
            polynomial.map_sub, polynomial.map_pow, polynomial.map_X, polynomial.map_mul, 
            polynomial.map_bit0, polynomial.map_one, polynomial.map_C, complex.of_real_eq_coe],
            have h_x_sub_exp : ∀ (x : ℕ), polynomial.X ^ 2 - 
            2 * 
            polynomial.C ↑((complex.exp (2 * ↑real.pi * (↑x / ↑n) * complex.I)).re) * 
            polynomial.X + 1 
            = (polynomial.X - 
            polynomial.C (complex.exp (2 * ↑real.pi * (↑x / ↑n) * complex.I))) * 
            (polynomial.X - 
            polynomial.C (complex.exp (2 * ↑real.pi * ((↑n - ↑x) / ↑n) * complex.I))),
            {
              intro x,
              have h_lift_ne_zero : (n : ℂ) ≠ 0,
              {
                simp only [ne.def, nat.cast_eq_zero],
                exact nat_ne_zero_of_pos hposn,
              },
              have h_free_term : 1 = 
              -polynomial.C (complex.exp (2 * ↑real.pi * (↑x / ↑n) * complex.I)) 
              * -polynomial.C (complex.exp (2 * ↑real.pi * ((↑n - ↑x) / ↑n) * complex.I)),
              {
                rw [neg_mul_neg, ← polynomial.C_mul, ← complex.exp_add,
                ← right_distrib, ← left_distrib, ← div_sub_div_same,
                sub_eq_neg_add, ← add_assoc, div_self, add_right_neg,
                zero_add, mul_one, complex.exp_mul_I, complex.cos_two_pi, 
                complex.sin_two_pi, zero_mul, add_zero, map_one],
                exact h_lift_ne_zero,
              },
              repeat { rw sub_eq_neg_add polynomial.X _, },
              rw right_distrib,
              repeat { rw left_distrib, },
              rw [← h_free_term, pow_two, sub_eq_neg_add, add_assoc, 
              add_comm (polynomial.X * polynomial.X) 1, ← add_assoc, ← add_assoc,
              add_right_cancel_iff,
              add_comm 1 (-polynomial.C (complex.exp (2 * ↑real.pi * (↑x / ↑n) * complex.I)) * polynomial.X),
              add_assoc, add_comm 1 (polynomial.X * -polynomial.C (complex.exp (2 * ↑real.pi * ((↑n - ↑x) / ↑n) * complex.I))),
              ← add_assoc, add_right_cancel_iff, neg_mul, mul_neg, polynomial.X_mul_C,
              ← neg_add, neg_inj, ← right_distrib, mul_eq_mul_right_iff],
              left,
              rw [← polynomial.C_add, two_mul, ← polynomial.C_add, polynomial.C_inj],
              simp only [complex.exp_mul_I, complex.add_re, complex.mul_re, 
              complex.I_re, mul_zero, complex.I_im, mul_one, zero_sub, 
              complex.of_real_add, complex.of_real_neg, sub_div, div_self h_lift_ne_zero,
              mul_sub, complex.sin_two_pi_sub, complex.cos_two_pi_sub],
              let t : ℝ := 2 * real.pi * (↑x / ↑n),
              have htdef : t = 2 * real.pi * (↑x / ↑n) := by refl,
              have ht : 2 * (real.pi : ℂ) * (↑x / ↑n) = ↑t,
              {
                rw htdef,
                simp only [complex.of_real_mul, complex.of_real_bit0, 
                complex.of_real_one, complex.of_real_div, complex.of_real_nat_cast,
                mul_eq_mul_left_iff, mul_eq_zero, bit0_eq_zero, one_ne_zero, 
                complex.of_real_eq_zero, false_or],
                left,
                rw [div_left_inj' h_lift_ne_zero, ← zmod.int_cast_cast,
                 ← complex.of_real_int_cast, zmod.int_cast_cast],
              },
              repeat { rw ht, },
              simp only [← complex.of_real_cos, ← complex.of_real_sin,
              complex.cos_of_real_re, complex.cos_of_real_im,
              complex.sin_of_real_re, complex.sin_of_real_im,
              complex.of_real_re, complex.of_real_im],
              rw [add_comm ↑(real.cos t) (-↑(real.sin t) * complex.I),
              ← add_assoc, ← add_assoc, 
              add_assoc ↑(real.cos t) (↑(real.sin t) * complex.I) 
              (-↑(real.sin t) * complex.I), ← right_distrib, add_neg_self, zero_mul],
              simp only [complex.of_real_zero, neg_zero', add_zero],
            },
            simp_rw h_x_sub_exp,
            rw finset.prod_mul_distrib,
            have h_prod_eq_prod : (finset.filter (λ (i : (zmod n)ˣ), 2 * ↑(i : zmod n) < (n : ℤ)) finset.univ).prod 
            (λ (x : (zmod n)ˣ), polynomial.X - 
            polynomial.C (complex.exp (2 * ↑real.pi * ((↑n - ↑x) / ↑n) * complex.I))) =
            (finset.filter (λ (i : (zmod n)ˣ), 2 * ↑(i : zmod n) > (n : ℤ)) finset.univ).prod 
            (λ (x : (zmod n)ˣ), polynomial.X - 
            polynomial.C (complex.exp (2 * ↑real.pi * (↑x / ↑n) * complex.I))),
            {
              --  (i : Π (a : α), a ∈ s → γ)
              apply finset.prod_bij' (λ i h, _),
            },
            rw h_prod_eq_prod,
            rw ← finset.prod_union,
            {
              rw finset.filter_union_right,
              simp_rw [← ne_iff_lt_or_gt],
              have h_ne_iff_true : ∀ (i : (zmod n)ˣ), 
              2 * ↑(i : zmod n) ≠ (n : ℤ) ↔ true,
              {
                intro i,
                simp only [ne.def, iff_true],
                intro h,
                rw mul_comm at h,
                have h_dvd : 2 ∣ (n : ℤ),
                { 
                  use ((i : zmod n) : ℤ),
                  rw [← h, mul_comm], 
                },
                have h_gcd : ((i : zmod n).val * 2).gcd n = 2,
                {
                  rw nat.gcd_mul_of_coprime_of_dvd,
                  { exact zmod.val_coe_unit_coprime i, },
                  { 
                    cases h_dvd with d h_dvd, 
                    cases d,
                    {
                      use d,
                      simp only [int.of_nat_eq_coe] at h_dvd,
                      rw [← nat.cast_two, ← nat.cast_mul] at h_dvd,
                      exact nat.cast_injective h_dvd,
                    },
                    {
                      exfalso,
                      have h_nonneg : 0 ≤ 2 * -[1+ d],
                      {
                        rw ← h_dvd,
                        exact nat.cast_nonneg n,
                      },
                      have h_neg : 2 * -[1+ d] < 0,
                      { exact int.mul_neg_of_pos_of_neg zero_lt_two (int.neg_succ_lt_zero d), },
                      exact not_lt_of_le h_nonneg h_neg,
                    }
                  }
                },
                have h_ne_zero : ne_zero n,
                { rw ne_zero_iff, exact nat_ne_zero_of_pos hposn, },
                apply n_ne_two,
                rw ← h_gcd,
                sorry,
                -- rw zmod.cast_eq_val at h,
              },
              simp_rw [h_ne_iff_true, finset.filter_true],
            },
            {
              intros a h1 h2,
              simp only [gt_iff_lt, finset.mem_filter, finset.mem_univ, true_and] at h1 h2,
              have h_lt_self : (n : ℤ) < (n : ℤ),
              { exact lt_trans h2 h1, }, 
              simp only [lt_self_iff_false] at h_lt_self,
              exact h_lt_self,
            }
          }
        },
        {
          intros r1 r2 h,
          dsimp at h,
          simp only [complex.of_real_inj] at h,
          exact h,
        }
      },
      have h_le_in_R : ↑(polynomial.eval (a : ℤ) (polynomial.cyclotomic n ℤ)) ≤ 
      ((a + 1) ^ (n.totient) : ℝ),
      {
        sorry,
      },
      rw [← int.cast_one, ← int.cast_add, ← int.cast_pow, int.cast_le] at h_le_in_R,
      exact h_le_in_R,
    }
  }
end