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
    apply int.coe_nat_inj,
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

lemma pow_ord_lemma : ∀ (e ≥ 1), ∀ {a b : ℕ}, a ^ e < b ^ e → a < b :=
  begin
    intros e e_ge_1 a b h',
    by_contra' h₁,
    cases eq_or_lt_of_le h₁ with h₁ h₁,
    {
      rw ←h₁ at h',
      simp at h',
      exact h',
    },
    {
      have h := lt_trans h' (nat.pow_lt_pow_of_lt_left h₁ e_ge_1),
      simp at h,
      exact h,
    },
  end

lemma ord_lemma : ∀ n : ℕ, ¬ ∃ m : ℕ, n < m ∧ m < n + 1 :=
  begin
    rintros n ⟨m, h⟩,
    have h := lt_of_le_of_lt ((by linarith) : n + 1 ≤ m) h.2,
    simp at h,
    exact h,
  end

  lemma sord_mul_lem : ∀ {a b c d : ℕ}, a < c → b < d → a * b < c * d :=
  begin
    intros a b c d,
    revert a b c,
    induction d,
    {
      introv,
      intros _ h,
      exfalso,
      simp at h,
      exact h,
    },
    {
      introv,
      intros h₁ h₂,
      by_cases h₃ : b < d_n,
      {
        have i : c * d_n.succ = c * d_n + c,
        refl,
        rw i,
        specialize d_ih a b c h₁ h₃,
        apply lt_trans d_ih,
        simp,
        cases c,
        {
          exfalso,
          simp at h₁,
          exact h₁,
        },
        {
          simp,
        },
      },
      {
        cases eq_or_lt_of_le ((lt_succ_iff.mp h₂) : b ≤ d_n) with h h,
        {

          rw ←h,
          induction c,
          {
            exfalso,
            simp at h₁,
            exact h₁,
          },
          {
            by_cases h₄ : a < c_n,
            {

              rw add_one_mul,
              apply lt_trans (c_ih h₄),
              apply lt_add_of_pos_right,
              simp,
            },
            {
              cases eq_or_lt_of_le ((lt_succ_iff.mp h₁) : a ≤ c_n) with h' h',
              {
                
                rw ←h',
                rw add_one_mul,
                rw (_ : a * b.succ = a * b + a),
                rw nat.add_assoc (a * b) a b.succ,
                apply lt_add_of_pos_right,
                simp,
                refl,
              },
              {
                exfalso,
                exact h₄ h',
              }

            },
          }
        },
        {
          exfalso,
          exact h₃ h,
        },
      },
    },
  end

lemma ord_mul_lem : ∀ {a b c d : ℕ}, a ≥ b → c ≥ d → a * c ≥ b * d :=
  begin
    introv,
    intros h h',
    cases eq_or_lt_of_le h with h₁ h₁;
    cases eq_or_lt_of_le h' with h₂ h₂,
    repeat {
      rw h₁,
      apply nat.mul_le_mul_left _,
      exact h',
    },
    repeat {
      rw h₂,
      apply nat.mul_le_mul_right _,
      exact h,
    },
    have := sord_mul_lem h₁ h₂,
    linarith,
  end