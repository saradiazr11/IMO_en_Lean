-- IMO 1962 Q4
-- Resolver la ecuación cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 = 1`

import analysis.special_functions.trigonometric

open real
open_locale real
noncomputable theory

def problema (x : ℝ) : Prop :=
cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 = 1

def funAuxiliar (x : ℝ) : ℝ :=
cos x * (cos x ^ 2 - 1/2) * cos (3 * x)

lemma Igualdad {x : ℝ} :
  (cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 - 1) / 4 = funAuxiliar x :=
begin
  rw funAuxiliar,
  rw real.cos_two_mul,
  rw cos_three_mul,
  ring,
end

lemma Equivalencia
  {x : ℝ}
  : problema x ↔ funAuxiliar x = 0 :=
begin
  split,
  { intro h1,
    rw problema at h1,
    rw ← Igualdad,
    rw div_eq_zero_iff,
    norm_num,
    rw sub_eq_zero,
    exact h1, },
  { intro h2,
    rw problema,
    rw ← Igualdad at h2,
    rw div_eq_zero_iff at h2,
    norm_num at h2,
    rw sub_eq_zero at h2,
    exact h2, },
end

lemma CasosSolucion
  {x : ℝ}
  : funAuxiliar x = 0 ↔ cos x ^ 2 = 1/2 ∨ cos (3 * x) = 0 :=
begin
  rw funAuxiliar,
  rw mul_assoc,
  rw mul_eq_zero,
  rw mul_eq_zero,
  rw sub_eq_zero,
  split,
  { intro h1,
    cases h1 with h11 h12,
    right,
    rw cos_three_mul,
    rw h11,
    ring,
    exact h12,},
  { intro h2,
    right,
    exact h2,},
end

lemma SolucionCosenoCuadrado
  {x : ℝ}
  : cos x ^ 2 = 1/2 ↔ ∃ k : ℤ, x = (2 * ↑k + 1) * π / 4 :=
begin
  rw cos_square,
  rw add_right_eq_self,
  rw div_eq_zero_iff,
  norm_num,
  split,
  { intro h1,
    rw cos_eq_zero_iff at h1,
    cases h1 with k1 hk1,
    use k1,
    linarith, },
  { intro h2,
    cases h2 with k2 hk2,
    rw cos_eq_zero_iff,
    use k2,
    linarith,},
end

lemma SolucionCosenoTriple
  {x : ℝ}
  : cos (3 * x) = 0 ↔ ∃ k : ℤ, x = (2 * ↑k + 1) * π / 6 :=
begin
  rw cos_eq_zero_iff,
  split,
  { intro h1,
    cases h1 with k1 hk1,
    use k1,
    linarith,},
  { intro h2,
    cases h2 with k2 hk2,
    use k2,
    linarith,},
end

def Solucion : set ℝ :=
{x : ℝ | ∃ k : ℤ, x = (2 * ↑k + 1) * π / 4 ∨ x = (2 * ↑k + 1) * π / 6}

theorem imo1962_q4
  {x : ℝ}
  : problema x ↔ x ∈ Solucion :=
begin
  rw Equivalencia,
  rw CasosSolucion,
  rw SolucionCosenoTriple,
  rw SolucionCosenoCuadrado,
  rw Solucion,
  exact exists_or_distrib.symm,
end
