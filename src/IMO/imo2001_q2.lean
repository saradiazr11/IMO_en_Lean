import analysis.special_functions.pow

/-!
Sean a, b y c tres números reales y positivos. Demostrar que
\frac{a}{\sqrt{a^2 + 8bc}} +
\frac{b}{\sqrt{b^2 + 8ca}} +
\frac{c}{\sqrt{c^2 + 8ab}} ≥ 1.
-/

open real

variables {a b c : ℝ}

lemma suma_pos
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  : 0 < a ^ 4 + b ^ 4 + c ^ 4 :=
begin
  have ha1 : 0 < a ^ 4          := pow_pos ha 4,
  have hb1 : 0 < b ^ 4          := pow_pos hb 4,
  have hc1 : 0 < c ^ 4          := pow_pos hc 4,
  have sum1 : 0 < a ^ 4 + b ^ 4 := add_pos ha1 hb1,
  exact (add_pos sum1 hc1),
end

-- Una demostración alternativa del lema anterior es la siguiente:
example
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  : 0 < a ^ 4 + b ^ 4 + c ^ 4 :=
begin
  apply add_pos,
  { apply add_pos,
    { exact pow_pos ha 4 },
    { exact pow_pos hb 4 }},
  { exact pow_pos hc 4 },
end

lemma cota
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  : a ^ 4 / (a ^ 4 + b ^ 4 + c ^ 4) ≤
    a ^ 3 / sqrt ((a ^ 3) ^ 2 + 8 * b ^ 3 * c ^ 3) :=
begin
  have ha3 : 0 < a ^ 3 :=
    pow_pos ha 3,
  have ha32 : 0 ≤ (a ^ 3) ^ 2 :=
    pow_two_nonneg (a ^ 3),
  have hb8 : 0 < 8 * b ^ 3 :=
    mul_pos (by norm_num) (pow_pos hb 3),
  have hbc : 0 < 8 * b ^ 3 * c ^ 3 :=
    mul_pos hb8 (pow_pos hc 3),
  have hdenom1 : 0 < (a ^ 3) ^ 2 + 8 * b ^ 3 * c ^ 3 :=
    add_pos_of_nonneg_of_pos ha32 hbc,
  have hsqrt : 0 < sqrt ((a ^ 3) ^ 2 + 8 * b ^ 3 * c ^ 3) :=
    sqrt_pos.mpr hdenom1,
  have hdenom2 : 0 < a ^ 4 + b ^ 4 + c ^ 4 :=
    suma_pos ha hb hc,
  have hdenom3 : 0 ≤ a ^ 4 + b ^ 4 + c ^ 4 :=
    le_of_lt hdenom2,
  rw div_le_div_iff hdenom2 hsqrt,
  rw pow_succ',
  rw mul_assoc,
  apply mul_le_mul_of_nonneg_left _ (le_of_lt ha3),
  rw ← pow_succ',
  apply le_of_pow_le_pow _ hdenom3 zero_lt_two,
  rw mul_pow,
  rw sq_sqrt (le_of_lt hdenom1),
  rw ← sub_nonneg,
  have desarrollo :
    (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 -
       a ^ 2 * ((a ^ 3) ^ 2 + 8 * b ^ 3 * c ^ 3)
    = 2 * (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2 + (b ^ 4 - c ^ 4) ^ 2 +
      (2 * (a ^ 2 * b * c - b ^ 2 * c ^ 2)) ^ 2 :=
    by ring,
  have h1 : 0 ≤ (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2 :=
    pow_two_nonneg _,
  have h1' : 0 ≤ 2 * (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2:=
    mul_nonneg zero_le_two h1,
  have h2 : 0 ≤ (b ^ 4 - c ^ 4) ^ 2:=
    pow_two_nonneg _,
  have h3 : 0 ≤ (2 * (a ^ 2 * b * c - b ^ 2 * c ^ 2)) ^ 2 :=
    pow_two_nonneg _,
  have aux1 : 0 ≤ (b ^ 4 - c ^ 4) ^ 2 +
                  (2 * (a ^ 2 * b * c - b ^ 2 * c ^ 2)) ^ 2 :=
    add_nonneg h2 h3,
  have tesis : 0 ≤ 2 * (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2 +
                   ((b ^ 4 - c ^ 4) ^ 2 +
                    (2 * (a ^ 2 * b * c - b ^ 2 * c ^ 2)) ^ 2) :=
    add_nonneg h1' aux1,
  rw desarrollo,
  rw add_assoc,
  exact tesis,
end

theorem imo2001_q2_aux
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  : 1 ≤ a ^ 3 / sqrt ((a ^ 3) ^ 2 + 8 * b ^ 3 * c ^ 3) +
        b ^ 3 / sqrt ((b ^ 3) ^ 2 + 8 * c ^ 3 * a ^ 3) +
        c ^ 3 / sqrt ((c ^ 3) ^ 2 + 8 * a ^ 3 * b ^ 3) :=
begin
  have h1 : b ^ 4 + c ^ 4 + a ^ 4 = a ^ 4 + b ^ 4 + c ^ 4,
    by ring,
  have h2 : c ^ 4 + a ^ 4 + b ^ 4 = a ^4 + b ^ 4 + c ^ 4,
    by ring,
  have h3 : a ^ 4 / (a ^ 4 + b ^ 4 + c ^ 4) +
            b ^ 4 / (b ^ 4 + c ^ 4 + a ^ 4) ≤
            a ^ 3 / sqrt ((a ^ 3) ^ 2 + 8 * b ^ 3 * c ^ 3) +
            b ^ 3 / sqrt ((b ^ 3) ^ 2 + 8 * c ^ 3 * a ^ 3) :=
    add_le_add (cota ha hb hc) (cota hb hc ha),
  have h4 : a ^ 4 / (a ^ 4 + b ^ 4 + c ^ 4) +
            b ^ 4 / (b ^ 4 + c ^ 4 + a ^ 4) +
            c ^ 4 / (c ^ 4 + a ^ 4 + b ^ 4) ≤
            a ^ 3 / sqrt ((a ^ 3) ^ 2 + 8 * b ^ 3 * c ^ 3) +
            b ^ 3 / sqrt ((b ^ 3) ^ 2 + 8 * c ^ 3 * a ^ 3) +
            c ^ 3 / sqrt ((c ^ 3) ^ 2 + 8 * a ^ 3 * b ^ 3) :=
    add_le_add h3 (cota hc ha hb),
  have igualdad : a ^ 4 / (a ^ 4 + b ^ 4 + c ^ 4) +
                  b ^ 4 / (b ^ 4 + c ^ 4 + a ^ 4) +
                  c ^ 4 / (c ^ 4 + a ^ 4 + b ^ 4) = 1,
    { rw h1,
      rw h2,
      rw ← add_div,
      rw ← add_div,
      rw div_self,
      apply ne_of_gt,
      exact suma_pos ha hb hc,},
  rw igualdad at h4,
  exact h4,
end

theorem imo2001_q2
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  : 1 ≤ a / sqrt (a ^ 2 + 8 * b * c) +
        b / sqrt (b ^ 2 + 8 * c * a) +
        c / sqrt (c ^ 2 + 8 * a * b) :=
begin
  have h : ∀ {x : ℝ}, 0 < x → (x ^ (3 : ℝ)⁻¹) ^ 3 = x,
    { intros x hx,
      have h1 : 0 < 3 :=
        zero_lt_three,
      have h2 : ↑3 = (3 : ℝ) :=
        by norm_num,
      have htesis : (x ^ (↑3)⁻¹) ^ 3 = x :=
        rpow_nat_inv_pow_nat (le_of_lt hx) h1,
      rw h2 at htesis,
      exact htesis,},
  have aux :=
    imo2001_q2_aux (rpow_pos_of_pos ha 3⁻¹)
                   (rpow_pos_of_pos hb 3⁻¹)
                   (rpow_pos_of_pos hc 3⁻¹),
  rw h ha at aux,
  rw h hb at aux,
  rw h hc at aux,
  exact aux,
end
