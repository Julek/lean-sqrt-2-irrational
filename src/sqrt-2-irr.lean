import data.nat.prime
import tactic.field_simp
import tactic.linarith

import helper

open nat

theorem rootn_not_pn_irr :
  ∀ e n : ℕ, e ≥ 1 → ¬ (∃ m : ℕ, n = m^e) → 
    ∀ q : ℚ, q^e ≠ n := 
begin
  intros e n e_ge_1 not_perfect_pow q q_to_e_eq_n,
  
  by_cases q < 0 ∧ odd e,
  {
    have h₁ : ∀ e₁ : ℕ, odd e₁ → q ^ e₁ < 0,
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
          rw [←nat.add_one, nat.left_distrib],
          simp,
          rw [pow_succ, pow_succ, ←rat.mul_assoc, mul_neg_iff],
          left,
          split,
          {
            simp[h.1],
            linarith,
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
    
    specialize h₁ e h.2,
    rw q_to_e_eq_n at h₁,
    norm_cast at h₁,
    simp at h₁,
    exact h₁,
  },
  {
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
            rw [ge_iff_le, rat.num_nonneg_iff_zero_le],
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