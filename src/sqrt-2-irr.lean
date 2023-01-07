import algebra.group_power.order
import data.nat.prime
import tactic.field_simp
import tactic.linarith
import tactic.ring_exp

import helper

open nat

theorem rootn_not_pn_irr :
  ∀ e n : ℕ,
    ¬ (∃ m : ℕ, m^e = n) ↔ ∀ q : ℚ, q^e ≠ n := 
begin
  intros e n,
  split,
  {
    intros not_perfect_pow q q_to_e_eq_n,
    
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
        exact h₁,
      },
      {
        have h₂ : q.denom ∣ q.num.nat_abs :=
          begin
            cases e,
            {
              exfalso,
              apply not_perfect_pow,
              use 0,
              simp,
              simp at q_to_e_eq_n,
              norm_cast at q_to_e_eq_n,
              exact q_to_e_eq_n,
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
  },
  {
    rintros h ⟨m, h'⟩,
    have h := h m,
    norm_cast at h,
  },
end

def floor_root' (e n : ℕ) : ℕ → ℕ
| 0 := 0
| (k+1) := if k ^ e ≤ n then k else floor_root' k

def floor_root (e n : ℕ) : ℕ := floor_root' e n n


lemma floor_root_lemma (e : ℕ) (h : e ≥ 1): ∀ n : ℕ, (floor_root e n)^e ≤ n ∧ n < ((floor_root e n) + 1)^e :=
  begin
    intro n,
    unfold floor_root,
    have h₁ : ∀ m : ℕ, m ^ e ≥ n → floor_root' e n m ^ e ≤ n ∧ n < (floor_root' e n m + 1) ^ e,
    sorry,
    apply h₁ n,
    {
      cases n,
      {
        simp,
      },
      {
        induction e,
        {
          exfalso,
          simp at h,
          exact h,
        },
        { 
          cases e_n,
          {
            simp,
          },
          {
            rw pow_succ,
            conv {
              to_rhs,
              rw ←nat.one_mul n.succ,
            },
            apply ord_mul_lem,
            apply succ_le_succ,
            exact zero_le n,
            apply e_ih,
            apply succ_le_succ,
            exact zero_le e_n,
            intros m h₂,
            sorry,
          },
        },
      },
    },
  end

def is_perfect_pow (n e : ℕ) := ∃ m : ℕ, m ^ e = n

lemma is_pp_equiv_lemma (n e : ℕ) : is_perfect_pow n e ↔ (floor_root e n)^e = n :=
  begin
    split,
    {
      intro h,
      by_cases h' : e ≥ 1,
      {
        rcases h with ⟨m, h⟩,
        have h₁ : floor_root e n = m,
        rcases floor_root_lemma e h' n with ⟨h₂, h₃⟩,
        conv at h₂ {
          to_rhs,
          rw ←h,
          skip,
        },
        conv at h₃ {
          to_lhs,
          rw ←h,
          skip,
        },
        by_contra,
        cases eq_or_lt_of_le h₂ with h₂ h₂,
        {
          exact h (nat.pow_left_injective h' h₂),
        },
        {
          have h₂ := pow_ord_lemma e h' h₂,
          have h₃ := pow_ord_lemma e h' h₃,
          apply ord_lemma (floor_root e n),
          use m,
          exact ⟨h₂, h₃⟩,
        },
        {
          rw h₁,
          exact h,
        },
      },
      {
        have h₁ : e = 0,
        linarith,
        rw h₁,
        simp,
        rcases h with ⟨m, h⟩,
        rw h₁ at h,
        simp at h,
        exact h,
      },
    },
    {
      intro h,
      use floor_root e n,
      exact h,
    }
  end

instance is_perfect_pow_dec (n e : ℕ) : decidable (is_perfect_pow n e) :=
  decidable_of_iff _ (iff.symm $ is_pp_equiv_lemma n e)

instance has_no_rational_root_dec (n e : ℕ) : decidable (∀ q : ℚ, q^e ≠ ↑n) :=
  begin
    haveI inst : decidable (∃ (m : ℕ), m ^ e = n) := 
      eq.rec (is_perfect_pow_dec n e) 
      (by refl : is_perfect_pow n e = (∃ (m : ℕ), m ^ e = n)),
    apply decidable_of_iff _ (rootn_not_pn_irr e n), 
  end

theorem sqrt_2_irr : ∀ q : ℚ, q^2 ≠ 2 := 
  begin
    have h : (2 : ℚ) = ↑(2 : ℕ) := by norm_cast,
    rw h,
    dec_trivial,
  end 

example : ∀ q : ℚ, q^2 ≠ ↑5 := dec_trivial