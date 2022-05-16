import data.nat.prime
import tactic.field_simp
import tactic.linarith

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