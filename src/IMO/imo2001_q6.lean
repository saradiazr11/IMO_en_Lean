/-AUTORES: Sara Díaz Real y José Antonio Alonso Jiménez-/

import data.int.basic
import tactic.ring
import data.int.parity
import algebra.associated
variables {a b c d : ℤ}

/-Sean a, b, c y d cuatro números enteros tales que
a > b > c > d > 0. Supongamos que
ac + bd = (a + b − c + d)(−a + b + c + d).
Demostrar que ab + cd no es primo.

Demostrar que ab + cd no es primo es equivalente
a probar que tiene algún divisor distinto de 1 y de
sí mismo.

En este caso se va a demostrar que el divisor es (ac +bd).
-/

lemma sumas_equivalentes
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (hd : 0 < d)
  (hba : b < a)
  (hcb : c < b)
  (hdc : d < c)
  (h : a*c + b*d = (a + b - c +d)*(-a + b + c + d))
  : b ^ 2 + b*d + d ^ 2 = a ^ 2 - a*c + c ^ 2 :=
  begin
    have h1: (a + b - c +d)*(-a + b + c + d)=
    -a ^ 2  + b ^ 2  + a*c - c ^ 2 + b*d + d ^2 + a*c + b*d
    := by ring,
    rw h1 at h,
    have h2: a*c = -a ^ 2 +  b ^ 2 + a * c - c ^ 2 + b * d + d ^ 2 + a * c,
    from add_right_cancel h,
    rw ← zero_add (a * c) at h2,
    have h3: 0 + a * c = -a ^ 2 + b ^ 2 + a * c - c ^ 2 + b * d + d ^ 2 + a * c,
    {rw zero_add,
    rw zero_add at h2,
    exact h2,},
    have h4: 0 = -a ^ 2 +  b ^ 2 + a * c - c ^ 2 + b * d + d ^ 2,
    from add_right_cancel h3,
    have h5: -a ^ 2 +  b ^ 2 + a * c - c ^ 2 + b * d + d ^ 2 = 
    - (a ^ 2 -a * c + c ^ 2) +  b ^ 2 + b * d + d ^ 2:= by ring,
    rw h5 at h4,
    rw ← sub_eq_zero,
    rw h4,
    ring,
  end

  lemma productos_equivalentes
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (hd : 0 < d)
  (hba : b < a)
  (hcb : c < b)
  (hdc : d < c)
  (h : a*c + b*d = (a + b - c +d)*(-a + b + c + d))
  : (a*c + b*d)*(b ^ 2 + b*d +d ^ 2) = (a*b + c*d)*(a*d + b*c) :=
  begin
    have h1: (a*c + b*d)*(b ^ 2 + b*d +d ^ 2) = a*c * (b ^ 2 + b*d +d ^ 2)
      + b*d*(b ^ 2 + b*d +d ^ 2):= by ring,
    have h2: a*c * (b ^ 2 + b*d +d ^ 2)
      + b*d*(b ^ 2 + b*d +d ^ 2)= a*c * (b ^ 2 + b*d +d ^ 2)
      + b*d*(a ^ 2 - a*c + c ^ 2),
      {rw sumas_equivalentes ha hb hc hd hba hcb hdc h,},
    rw h2 at h1,
    have h3: a * c * (b ^ 2 + b * d + d ^ 2) + b * d * (a ^ 2 - a * c + c ^ 2)
    = a*c*b ^ 2 + a*c*d ^ 2 + a ^ 2 * b * d + b * c ^ 2 * d, by ring,
    rw h3 at h1,
    have h4: a*c*b ^ 2 + a*c*d ^ 2 + a ^ 2 * b * d + b * c ^ 2 * d
    = (a*b + c*d)*(a*d + b*c), by ring,
    rw h4 at h1,
    exact h1,
    end

lemma desigualdad_auxiliar1
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (hd : 0 < d)
  (hba : b < a)
  (hcb : c < b)
  (hdc : d < c)
  (h : a*c + b*d = (a + b - c +d)*(-a + b + c + d))
  : a * c + b * d < a * b + c * d:=
  begin
    have h1: (a * b + c * d) - (a * c + b * d) = (a - d) * (b - c), by ring,
    have h2: 0 < a - d ,
    { have h21: c < a, from lt_trans hcb hba,
      have h22: d < a, from lt_trans hdc h21,
      rw ← sub_pos at h22,
      exact h22,},
    have h3: 0 < b - c,
    { rw sub_pos,
      exact hcb,},
    have h4: 0 < (a - d) * (b - c), from mul_pos h2 h3,
    rw ← sub_pos,
    rw h1,
    exact h4,
  end

  lemma desigualdad_auxiliar2
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (hd : 0 < d)
  (hba : b < a)
  (hcb : c < b)
  (hdc : d < c)
  (h : a*c + b*d = (a + b - c +d)*(-a + b + c + d))
  : a * d + b * c < a * c + b * d:=
  begin
    have h1: (a * c + b * d) - (a * d + b * c) = (a - b) * (c - d), by ring,
    have h2: 0 < a - b,
    { rw sub_pos,
      exact hba,},
    have h3: 0 < c - d,
    { rw sub_pos,
      exact hdc,},
    have h4: 0 < (a - b) * (c - d), from mul_pos h2 h3,
    rw ← sub_pos,
    rw h1,
    exact h4,
  end

  lemma division
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (hd : 0 < d)
  (hba : b < a)
  (hcb : c < b)
  (hdc : d < c)
  (h : a*c + b*d = (a + b - c +d)*(-a + b + c + d)):
  (a*c+b*d) ∣ (a*b+c*d)*(a*d+b*c):=
  begin
    use (b ^ 2 + b*d +d ^ 2),
    symmetry,
    exact (productos_equivalentes ha hb hc hd hba hcb hdc h),
  end


  theorem imo2001q6
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (hd : 0 < d)
  (hba : b < a)
  (hcb : c < b)
  (hdc : d < c)
  (h : a*c + b*d = (a + b - c + d)*(-a + b + c + d))
  : ¬ prime (a*b + c*d) :=
begin
  intro h1,
  have h2:= productos_equivalentes ha hb hc hd hba hcb hdc h,
  have h3:= division ha hb hc hd hba hcb hdc h,
  have h4: ((a*b + c*d) ∣ (a * c + b * d)) ∨ ((a * c + b * d)  ∣ (a * d + b * c)),
  from left_dvd_or_dvd_right_of_dvd_prime_mul h1 h3,
  cases h4 with hj hk,
  { have hj1: a * b + c * d >  a * c + b * d, 
      from desigualdad_auxiliar1 ha hb hc hd hba hcb hdc h,
    have hpj: 0 < a * c + b * d,
      from add_pos (mul_pos ha hc) (mul_pos hb hd),
    have hj2: a * b + c * d ≤  a * c + b * d, 
      from int.le_of_dvd hpj hj,
    have hj3: ¬ (a * b + c * d ≤  a * c + b * d), from not_le.mpr hj1,
    exact hj3 hj2,},
  { have hk1: a*c+b*d > a*d+b*c, 
      from desigualdad_auxiliar2 ha hb hc hd hba hcb hdc h,
    have hpk: 0 < a * d + b * c,
      from add_pos (mul_pos ha hd) (mul_pos hb hc),
    have hk2: a * c + b * d ≤ a * d + b * c,
      from int.le_of_dvd hpk hk,
    have hk3: ¬ (a*c+b*d ≤  a*d+b*c), from not_le.mpr hk1,
    exact hk3 hk2,},
end