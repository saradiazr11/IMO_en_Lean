import analysis.special_functions.pow

/-!
Sean a, b y c tres números reales y positivos. Demostrar que
\frac{a}{\sqrt{a^2 + 8bc}} +
\frac{b}{\sqrt{b^2 + 8ca}} +
\frac{c}{\sqrt{c^2 + 8ab}} ≥ 1.
-/

open real

variables {a b c : ℝ}

lemma suma_pos (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  0 < a ^ 4 + b ^ 4 + c ^ 4 :=
begin
  have ha1: 0 < a ^ 4:=pow_pos ha 4,
  have hb1: 0 < b ^ 4:=pow_pos hb 4,
  have hc1: 0 < c ^ 4:=pow_pos hc 4,
  have sum1: 0< a ^ 4 + b ^ 4 := add_pos ha1 hb1,
  have sum2: 0< a ^ 4 + b ^ 4 + c ^ 4 := add_pos sum1 hc1,
  exact sum2,
end
/--/
lemma cota (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  a ^ 4 / (a ^ 4 + b ^ 4 + c ^ 4) ≤
  a ^ 3 / sqrt ((a ^ 3) ^ 2 + 8 * b ^ 3 * c ^ 3) :=
begin
  have ha3: 0 < a ^ 3:= pow_pos ha 3,
  have ha32: 0 < (a ^ 3) ^ 2:= pow_pos ha3 2,
  have hb8: 0 < 8 * b ^ 3 := mul_pos (bit0_pos zero_lt_four) (pow_pos hb 3),
  have hsqrt: 0 < 8 * b ^ 3 * c ^ 3 := mul_pos hb8 (pow_pos hc 3),
  have hdenom := suma_pos ha hb hc,
  
end-/

lemma bound (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  a ^ 4 / (a ^ 4 + b ^ 4 + c ^ 4) ≤
  a ^ 3 / sqrt ((a ^ 3) ^ 2 + 8 * b ^ 3 * c ^ 3) :=
begin
  have hsqrt := add_pos_of_nonneg_of_pos (pow_two_nonneg (a ^ 3))
    (mul_pos (mul_pos (bit0_pos zero_lt_four) (pow_pos hb 3)) (pow_pos hc 3)),
  have hdenom := suma_pos ha hb hc,
  rw div_le_div_iff hdenom (sqrt_pos.mpr hsqrt),
  conv_lhs { rw [pow_succ', mul_assoc] },
  apply mul_le_mul_of_nonneg_left _ (pow_pos ha 3).le,
  apply le_of_pow_le_pow _ hdenom.le zero_lt_two,
  rw [mul_pow, sq_sqrt hsqrt.le, ← sub_nonneg],
  calc  (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 - a ^ 2 * ((a ^ 3) ^ 2 + 8 * b ^ 3 * c ^ 3)
      = 2 * (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2 + (b ^ 4 - c ^ 4) ^ 2 +
        (2 * (a ^ 2 * b * c - b ^ 2 * c ^ 2)) ^ 2 : by ring
  ... ≥ 0 : add_nonneg (add_nonneg (mul_nonneg zero_le_two (pow_two_nonneg _))
              (pow_two_nonneg _)) (pow_two_nonneg _)
end

theorem imo2001_q2' (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  1 ≤ a ^ 3 / sqrt ((a ^ 3) ^ 2 + 8 * b ^ 3 * c ^ 3) +
      b ^ 3 / sqrt ((b ^ 3) ^ 2 + 8 * c ^ 3 * a ^ 3) +
      c ^ 3 / sqrt ((c ^ 3) ^ 2 + 8 * a ^ 3 * b ^ 3) :=
have h₁ : b ^ 4 + c ^ 4 + a ^ 4 = a ^ 4 + b ^ 4 + c ^ 4,
  by rw [add_comm, ← add_assoc],
have h₂ : c ^ 4 + a ^ 4 + b ^ 4 = a ^ 4 + b ^ 4 + c ^ 4,
  by rw [add_assoc, add_comm],
calc _ ≥ _ : add_le_add (add_le_add (bound ha hb hc) (bound hb hc ha)) (bound hc ha hb)
   ... = 1 : by rw [h₁, h₂, ← add_div, ← add_div, div_self $ ne_of_gt $ auma_pos ha hb hc]

theorem imo2001_q2 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
  1 ≤ a / sqrt (a ^ 2 + 8 * b * c) +
      b / sqrt (b ^ 2 + 8 * c * a) +
      c / sqrt (c ^ 2 + 8 * a * b) :=
have h3 : ∀ {x : ℝ}, 0 < x → (x ^ (3 : ℝ)⁻¹) ^ 3 = x :=
  λ x hx, show ↑3 = (3 : ℝ), by norm_num ▸ rpow_nat_inv_pow_nat hx.le zero_lt_three,
calc 1 ≤ _ : imo2001_q2' (rpow_pos_of_pos ha _) (rpow_pos_of_pos hb _) (rpow_pos_of_pos hc _)
   ... = _ : by rw [h3 ha, h3 hb, h3 hc]