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
    
    by_cases h : q < 0 ∧ odd e,
    { 
      have h₁ := neg_odd_pow_lemma h.1 h.2,
      rw q_to_e_eq_n at h₁,
      norm_cast at h₁,
      exact nat.not_lt_zero n h₁,
    },
    {
      have h₁ : q.num.nat_abs^e = n * q.denom^e :=
        begin
          rw rat.eq_iff_mul_eq_mul at q_to_e_eq_n,
          norm_cast at q_to_e_eq_n,
          rw [mul_one, cast_mul] at q_to_e_eq_n,
          rw ← int.coe_nat_eq_coe_nat_iff,
          field_simp,
          cases ((by tauto!) : ¬(q < 0) ∨ ¬(odd e)) with h' h',
          {
            have q_num_ge_0 : q.num ≥ 0,
            {
              rw [ge_iff_le, rat.num_nonneg_iff_zero_le],
              exact not_lt.1 h',
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
        rw [h, one_pow, mul_one] at h₁,
        apply not_perfect_pow,
        exact ⟨q.num.nat_abs, h₁⟩,
      },
      {
        have h₂ : q.denom ∣ q.num.nat_abs :=
          begin
            cases e,
            {
              exfalso,
              apply not_perfect_pow,
              rw pow_zero at q_to_e_eq_n,
              norm_cast at q_to_e_eq_n,
              rw ← q_to_e_eq_n,
              use 0,
              rw pow_zero,
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
| k'@(k+1) := if k' ^ e ≤ n then k' else floor_root' k

def floor_root (e n : ℕ) : ℕ := floor_root' e n n


lemma floor_root_lemma (e : ℕ) (h : e ≥ 1): ∀ n : ℕ, (floor_root e n)^e ≤ n ∧ n < ((floor_root e n) + 1)^e :=
  begin
    intro n,
    unfold floor_root,
    {
      have h₁ : ∀ e n m : ℕ, e ≥ 1 → (m + 1) ^ e > n → floor_root' e n m ^ e ≤ n ∧ n < (floor_root' e n m + 1) ^ e,
      {
        introv,
        revert e_1 n_1,
        induction m,
        {
          introv,
          intros e_ge_1 h₁,
          cases e_1,
          {
            linarith,
          },
          {
            rw [one_pow, gt_iff_lt, lt_one_iff] at h₁,
            unfold floor_root',
            simp only 
              [
                h₁, zero_pow', ne.def, succ_ne_zero, not_false_iff, 
                le_zero_iff, one_pow, lt_one_iff, and_self
              ],
          },
        },
        {
          introv,
          intros e_ge_1 h₁,
          unfold floor_root',
          split_ifs,
          {
            refine ⟨h_1,h₁⟩,
          },
          {
            exact m_ih _ _ e_ge_1 (by linarith),
          },
        },
      },
      apply h₁ e n n h,
      {
        cases n,
        {
          rw [one_pow, gt_iff_lt, lt_one_iff],
        },
        {
          induction e,
          {
            linarith,
          },
          { 
            cases e_n,
            {
              rw [pow_one, gt_iff_lt, lt_add_iff_pos_right, lt_one_iff],
            },
            {
              rw pow_succ,
              conv {
                to_rhs,
                rw ←nat.one_mul n.succ,
              },
              apply sord_mul_lem,
              {
                exact one_lt_succ_succ n,
              },
              {
                apply e_ih,
                apply succ_le_succ,
                exact zero_le e_n,
              },
            },
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
        {
          rcases floor_root_lemma e h' n with ⟨h₂, h₃⟩,
          conv at h₂ {
            to_rhs,
            rw ←h,
          },
          conv at h₃ {
            to_lhs,
            rw ←h,
          },
          by_contra,
          cases eq_or_lt_of_le h₂ with h₂ h₂,
          {
            exact h (nat.pow_left_injective h' h₂),
          },
          {
            have h₂ := pow_ord_lemma e h' h₂,
            have h₃ := pow_ord_lemma e h' h₃,
            exact ord_lemma (floor_root e n) ⟨m, h₂, h₃⟩,
          },
        },
        {
          rw h₁,
          exact h,
        },
      },
      {
        have h₁ : e = 0,
        linarith,
        rw h₁ at *,
        rcases h with ⟨m, h⟩,
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

example : ∀ q : ℚ, q^5 ≠ ↑101 := dec_trivial