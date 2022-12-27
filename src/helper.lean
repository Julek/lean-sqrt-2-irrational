import algebra.parity
import data.nat.parity
import data.nat.prime
import data.rat

open nat 

lemma rat_pow_denom_lemma : 
      ∀ a b : ℚ, coprime a.num.nat_abs b.denom → 
        coprime b.num.nat_abs a.denom → 
        (a * b).denom = a.denom * b.denom :=
  begin
    introv,
    intros a_num_cop_b_denom b_num_cop_a_denom,
    cases a,
    cases b,
    rw rat.mul_num_denom,
    simp at *,
    norm_cast,
    have h₁ : (↑(a_denom * b_denom) : ℤ) > 0,
    {
      norm_cast,
      simp,
      exact ⟨a_pos, b_pos⟩,
    },
    have h₂ : coprime (a_num * b_num).nat_abs (↑(a_denom * b_denom) : ℤ).nat_abs,
    {
      norm_cast,
      have h₃ := nat.coprime.mul a_cop b_num_cop_a_denom,
      have h₄ := nat.coprime.mul b_cop a_num_cop_b_denom,
      rw ←int.nat_abs_mul at h₃,
      rw [←int.nat_abs_mul, int.mul_comm] at h₄,
      exact nat.coprime.mul_right h₃ h₄,
    },
    have h₃ : ∀ {a b : ℕ}, (↑a : ℤ) = (↑b : ℤ) → a = b,
    {
      intros a b h,
      unfold coe at h, unfold lift_t at h, unfold has_lift_t.lift at h,
      unfold coe_t at h, unfold has_coe_t.coe at h, unfold coe_b at h,
      unfold has_coe.coe at h,
      injection h,
    },
    apply h₃,
    cases ↑(a_denom * b_denom),
    {
      delta rat.mk,
      simp,
      delta id_rhs,
      unfold rat.mk_nat,
      split_ifs,
      {
        exfalso,
        rw h at h₁,
        simp at h₁,
        exact h₁,
      },
      {
        unfold rat.mk_pnat,
        simp,
        unfold coprime at h₂,
        rw int.nat_abs_of_nat_core at h₂,
        rw h₂,
        simp,
      },
    },
    {
      exfalso,
      simp at h₁,
      exact h₁,
    },
  end

lemma rat_pow_num_lemma : 
      ∀ a b : ℚ, coprime a.num.nat_abs b.denom → 
        coprime b.num.nat_abs a.denom → 
        (a * b).num = a.num * b.num :=
  begin
    introv,
    intros h h',
    cases a,
    cases b,
    rw rat.mul_num_denom,
    simp at *,
    norm_cast,
    have h₁ : (↑(a_denom * b_denom) : ℤ) > 0,
    {
      norm_cast,
      simp,
      exact ⟨a_pos, b_pos⟩,
    },
    have h₂ : coprime (a_num * b_num).nat_abs (↑(a_denom * b_denom) : ℤ).nat_abs,
    {
      norm_cast,
      have h₃ := nat.coprime.mul a_cop h',
      have h₄ := nat.coprime.mul b_cop h,
      rw ←int.nat_abs_mul at h₃,
      rw [←int.nat_abs_mul, int.mul_comm] at h₄,
      exact nat.coprime.mul_right h₃ h₄,
    }, 
    cases ↑(a_denom * b_denom),
    {
      rw int.nat_abs_of_nat_core at h₂,
      delta rat.mk,
      simp,
      delta id_rhs,
      unfold rat.mk_nat,
      split_ifs,
      {
        exfalso,
        rw h_1 at h₁,
        simp at h₁,
        exact h₁,
      },
      {
        unfold rat.mk_pnat,
        simp,
        unfold coprime at h₂,
        rw h₂,
        simp,
      },
    },
    {
      exfalso,
      simp at h₁,
      exact h₁,
    },
  end

lemma rat_pow_lemma (q : ℚ) (e : ℕ) : 
  (q ^ e).num = q.num ^ e ∧ (q ^ e).denom = q.denom ^ e :=
  begin
    induction e,
    {
      simp,
    },
    {
      repeat { rw pow_succ, },
      rw [←e_ih.1, ←e_ih.2, rat_pow_denom_lemma, rat_pow_num_lemma],
      split,
      repeat { refl, },
      repeat {
        rw e_ih.2,
        apply nat.coprime.pow_right _,
        exact q.cop,
      },
      repeat {
        rw [e_ih.1, int.nat_abs_pow],
        apply nat.coprime.pow_left _,
        exact q.cop,
      },
    },
  end

lemma abs_pow_eq_pow_of_even_exp : 
  ∀ {i : ℤ} {e : ℕ}, even e → ↑i.nat_abs ^ e = i ^ e :=
  begin
    intros i _ h,
    rw ←int.abs_eq_nat_abs,
    exact even.pow_abs h i,
  end