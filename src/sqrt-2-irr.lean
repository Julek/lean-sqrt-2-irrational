import data.nat.prime
import tactic.field_simp
import tactic.linarith

import helper

open nat

theorem sqrt_2_irr : ∀ q : ℚ, q^2 ≠ 2 := 
begin
  intro q,
  intro q_sqrd_eq_2,

  have h₁ : q.num.nat_abs^2 = 2 * q.denom^2 := 
  begin
    rw rat.eq_iff_mul_eq_mul at q_sqrd_eq_2,
    norm_cast at q_sqrd_eq_2,
    simp at q_sqrd_eq_2,
    rw ← int.coe_nat_eq_coe_nat_iff,
    field_simp,
    simp only [sq] at *,
    rw [rat.mul_self_num, rat.mul_self_denom] at q_sqrd_eq_2,
    exact q_sqrd_eq_2,
  end,

  have h₂ : 2 ∣ q.num.nat_abs := 
  begin
    have h : 2 ∣ 2*q.denom^2 := 
      by simp,
    rw ←h₁ at h,
    cases (prime.dvd_mul prime_two).1 h with h_1,
    exact h_1,
    rw [nat.add, npow_rec, npow_rec, mul_one] at h_1,
    exact h_1,
  end,

  have h₃ : 2 ∣ q.denom := 
    begin
      have h : 2*2 ∣ q.num.nat_abs ^ 2 := 
        by apply pow_dvd_pow_of_dvd h₂,
      rw h₁ at h,
      have h' : 2 ∣ q.denom ^ 2 := 
      begin
        apply @dvd_of_mul_dvd_mul_left _ _ 2,
        simp,
        assumption,
      end,
      cases (prime.dvd_mul prime_two).1 h',
      assumption,
      rw [nat.add, npow_rec, npow_rec, mul_one] at h_1,
      exact h_1,
    end,

  have h₄ : gcd q.num.nat_abs q.denom ≥ 2 := 
    begin
      apply exists.elim h₂,
      intros c_num q_num_eq_2_c_num,
      apply exists.elim h₃,
      intros c_denom q_denom_eq_c_denom,
      have c_denom_ge_1 : c_denom ≥ 1 := 
        by linarith [q.pos],
      rw [q_num_eq_2_c_num, q_denom_eq_c_denom, gcd_mul_left],
      have h₅ : 0 < c_num.gcd c_denom := 
        nat.gcd_pos_of_pos_right c_num c_denom_ge_1,
      linarith,
    end,

  have h₅ : gcd q.num.nat_abs q.denom = 1 := q.cop,
  
  linarith,
end  

theorem sqrt_not_ps_irr :
  ∀ n : ℕ, ¬ (∃ m : ℕ, n = m^2) → 
    ∀ q : ℚ, q^2 ≠ n := 
begin
  intros n n_not_perfect_square q q_sqrd_eq_n,

  have h₁ : q.num.nat_abs^2 = n * q.denom^2 :=
    begin
      rw rat.eq_iff_mul_eq_mul at q_sqrd_eq_n,
      norm_cast at q_sqrd_eq_n,
      simp at q_sqrd_eq_n,
      rw ← int.coe_nat_eq_coe_nat_iff,
      field_simp,
      simp only [sq] at *,
      rw [rat.mul_self_num, rat.mul_self_denom] at q_sqrd_eq_n,
      exact q_sqrd_eq_n,
    end,
  
  by_cases q.denom = 1,
  {
    simp[h] at h₁,
    apply n_not_perfect_square,
    use q.num.nat_abs,
    exact eq.symm h₁,
  },
  {
    have h₂ : q.denom ∣ q.num.nat_abs :=
      begin
        repeat {rw sq at h₁},
        apply nat.coprime.dvd_of_dvd_mul_left q.cop.symm,
        use (n * q.denom),
        rw h₁,
        ring,
      end,
  
    have q_cop := q.cop,
    unfold coprime at q_cop,
    rw nat.gcd_eq_right_iff_dvd.1 h₂ at q_cop, 
    exact h q_cop,
  },
end

theorem rootn_not_pn_irr :
  ∀ e n : ℕ, e ≥ 1 → ¬ (∃ m : ℕ, n = m^e) → 
    ∀ q : ℚ, q^e ≠ n := 
begin
  intros e n e_ge_1 not_perfect_pow q q_to_e_eq_n,
  
  by_cases q < 0 ∧ odd e;
  revert e,
  {
    intros e e_ge_1 not_perfect_pow q_to_e_eq_n h,
    have h' : ∀ e₁ : ℕ, odd e₁ → q ^ e₁ < 0,
    {
      intros e₁ e₁_odd,

      induction e₁ using nat.strong_induction_on with e₁ ih,
      {
        simp at ih,
        unfold odd at e₁_odd,
        rcases e₁_odd with ⟨k,h'⟩,
        rw h',
        cases k,
        {
          simp,
          exact h.1,
        },
        {
          rw ← nat.add_one,
          rw nat.left_distrib,
          simp,
          rw pow_succ,
          rw pow_succ,
          rw ←rat.mul_assoc,
          rw mul_neg_iff,
          left,
          split,
          {
            simp[h.1],
            intro h'',
            rw h'' at h,
            simp at h,
            exact h,
          },
          {
            apply ih (2 * k + 1),
            {
              rw h',
              simp,
              exact lt_add_one k,
            },
            {
              rw ←nat.odd_iff_not_even,
              unfold odd,
              use k,
            },
          },
        },
      },
    },
    
    specialize h' e h.2,
    rw q_to_e_eq_n at h',
    norm_cast at h',
    simp at h',
    exact h',
  },
  {
    intros e e_ge_1 not_perfect_pow q_to_e_eq_n h,
    have h₁ : q.num.nat_abs^e = n * q.denom^e :=
      begin
        rw rat.eq_iff_mul_eq_mul at q_to_e_eq_n,
        norm_cast at q_to_e_eq_n,
        simp at q_to_e_eq_n,
        rw ← int.coe_nat_eq_coe_nat_iff,
        field_simp,
        cases ((by tauto!) : ¬(q < 0) ∨ ¬(odd e)) with h' h',
        {
          simp at h',
          have q_num_ge_0 : q.num ≥ 0,
          {
            rw ge_iff_le,
            rw rat.num_nonneg_iff_zero_le,
            exact h',
          },
          norm_cast,
          rw 
            [
              (rat_pow_lemma _ _).1, 
              (rat_pow_lemma _ _).2, 
              ←int.nat_abs_of_nonneg q_num_ge_0
            ] at q_to_e_eq_n,
          norm_cast at q_to_e_eq_n,
          exact q_to_e_eq_n,
        },  
        {
          norm_cast,
          rw 
            [
              (rat_pow_lemma _ _).1, 
              (rat_pow_lemma _ _).2, 
              ←abs_pow_eq_pow_of_even_exp (nat.even_iff_not_odd.2 h')
            ] at q_to_e_eq_n,
          norm_cast at q_to_e_eq_n,
          exact q_to_e_eq_n,
        },
      end,

    by_cases q.denom = 1,
    {
      rw h at h₁,
      simp at h₁,
      apply not_perfect_pow,
      use q.num.nat_abs,
      exact eq.symm h₁,
    },
    {
      have h₂ : q.denom ∣ q.num.nat_abs :=
        begin
          cases e,
          {
            exfalso,
            simp at e_ge_1,
            exact e_ge_1,
          },
          {
            apply @nat.coprime.dvd_of_dvd_mul_left (q.num.nat_abs ^ e) q.num.nat_abs,
            exact coprime.pow_right e q.cop.symm,
            use (n * q.denom ^ e),
            conv {
              congr,
              rw [nat.mul_comm, ←pow_succ],
              skip,
              rw [nat.mul_comm, nat.mul_assoc],
              congr,
              skip,
              rw [nat.mul_comm, ←pow_succ],
              skip,
            },
            exact h₁,
          },
        end,
  
      have q_cop := q.cop,
      unfold coprime at q_cop,
      rw nat.gcd_eq_right_iff_dvd.1 h₂ at q_cop, 
      exact h q_cop,
    },
  },
end

lemma two_not_perfect_square : ¬∃ (m : ℕ), 2 = m ^ 2 :=
  begin
    intro h,
    rcases h with ⟨m, h'⟩,
    by_cases m > 1,
    {
      have h'' : m ^ 2 > 2,
      {
        have h₁ : m ^ 2 ≥ 2 * m,
        { 
          rw sq,
          apply nat.mul_le_mul_of_nonneg_right,
          linarith,
        },
        apply gt_of_ge_of_gt h₁,
        linarith,
      },
      rw ←h' at h'',
      simp at h'',
      exact h''
    },
    {
      have h'' : m = 0 ∨ m = 1,
      {
        cases m,
        {left, refl, },
        {
          cases m,
          {right, refl, },
          {
            exfalso,
            simp at h,
            exact h,
          },
        },
      },
      cases h'',
      repeat {
        rw h'' at h',
        simp at h',
        exact h',
      },
    },
  end

example : ∀ q : ℚ, q^2 ≠ 2 :=
  begin
    have h := rootn_not_pn_irr 2 2 (by simp) two_not_perfect_square,
    norm_cast at h,
    exact h,
  end