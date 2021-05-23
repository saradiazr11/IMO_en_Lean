/- Título:  Formalización del problema Q6 de la IMO de 2001
   Autor:   Sara Díaz Real
   Fecha:   22 de mayo de 2021
-/

-- El enunciado del problema Q6 de la IMO del 2001 es
--    Sean a, b, c y d números enteros tales que a > b > c > d > 0.
--    Supongamos que
--       ac + bd = (a + b - c + d)(-a + b + c + d).
--    Demostrar que ab + cd no es primo.
--
-- En esta teoría haremos la formalización de una solución de dicho
--    problema.

import data.int.basic
import tactic.ring
import data.int.parity
import algebra.associated
import tactic

variables {a b c d : ℤ}

lemma sumas_equivalentes
  (h : a*c + b*d = (a + b - c + d) * (-a + b + c + d))
  : b^2 + b*d + d^2 = a^2 - a*c + c^2 :=
begin
  have h1: (a + b - c + d) * (-a + b + c + d) =
           -a^2  + b^2  + a*c - c^2 + b*d + d^2 + a*c + b*d,
    by ring,
  rw h1 at h,
  by nlinarith,
end

lemma productos_equivalentes
  (h : a*c + b*d = (a + b - c + d) * (-a + b + c + d))
  : (a*c + b*d) * (b^2 + b*d + d^2) = (a*b + c*d) * (a*d + b*c) :=
begin
  have h1: (a*c + b*d) * (b^2 + b*d + d^2) =
           a*c * (b^2 + b*d + d^2) + b*d * (b^2 + b*d + d^2),
    by ring,
  have h2: a*c * (b^2 + b*d + d^2) + b*d * (b^2 + b*d + d^2) =
           a*c * (b^2 + b*d + d^2) + b*d * (a^2 - a*c + c^2),
    by rw sumas_equivalentes h,
  rw h2 at h1,
  by nlinarith,
end

lemma desigualdad_auxiliar1
  (hba : b < a)
  (hcb : c < b)
  (hdc : d < c)
  (h : a*c + b*d = (a + b - c + d) * (-a + b + c + d))
  : a*c + b*d < a*b + c*d:=
by nlinarith

lemma desigualdad_auxiliar2
  (hba : b < a)
  (hdc : d < c)
  (h : a*c + b*d = (a + b - c + d)*(-a + b + c + d))
  : a*d + b*c < a*c + b*d:=
by nlinarith

lemma division
  (h : a*c + b*d = (a + b - c + d) * (-a + b + c + d))
  : a*c + b*d ∣ (a*b+c*d) * (a*d+b*c):=
begin
  use (b^2 + b*d +d^2),
  by nlinarith [productos_equivalentes h],
end

theorem imo2001q6
  (hd  : 0 < d)
  (hdc : d < c)
  (hcb : c < b)
  (hba : b < a)
  (h : a*c + b*d = (a + b - c + d)*(-a + b + c + d))
  : ¬ prime (a*b + c*d) :=
begin
  intro h1,
  have ha : 0 < a,
    by linarith,
  have hb : 0 < b,
    by linarith,
  have hc : 0 < c,
    by linarith,
  have h2 : (a*c + b*d) * (b^2 + b*d + d^2) =
            (a*b + c*d) * (a*d + b*c),
    from productos_equivalentes h,
  have h3 : a*c + b*d ∣ (a*b + c*d) * (a*d + b*c),
    from division h,
  have h4: (a*b + c*d ∣ a*c + b*d) ∨ (a*c + b*d  ∣ a*d + b*c),
    from left_dvd_or_dvd_right_of_dvd_prime_mul h1 h3,
  cases h4 with hj hk,
  { have hj1: a*b + c*d > a*c + b*d,
      from desigualdad_auxiliar1 hba hcb hdc h,
    have hpj: 0 < a*c + b*d,
      from add_pos (mul_pos ha hc) (mul_pos hb hd),
    have hj2: a*b + c*d ≤ a*c + b*d,
      from int.le_of_dvd hpj hj,
    have hj3: ¬ (a*b + c*d ≤ a*c + b*d),
      from not_le.mpr hj1,
    exact hj3 hj2, },
  { have hk1: a*c + b*d > a*d + b*c,
      from desigualdad_auxiliar2 hba hdc h,
    have hpk: 0 < a*d + b*c,
      from add_pos (mul_pos ha hd) (mul_pos hb hc),
    have hk2: a*c + b*d ≤ a*d + b*c,
      from int.le_of_dvd hpk hk,
    have hk3: ¬ (a*c+b*d ≤  a*d+b*c),
      from not_le.mpr hk1,
    exact hk3 hk2, },
end
