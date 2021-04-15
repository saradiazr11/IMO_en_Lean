
import analysis.special_functions.trigonometric

/-!
# IMO 1962 Q4
Solve the equation `cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 = 1`.
Since Lean does not have a concept of "simplest form", we just express what is
in fact the simplest form of the set of solutions, and then prove it equals the set of solutions.
-/

open real
open_locale real
noncomputable theory

def problema (x : ℝ) : Prop := cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 = 1

def Solucion : set ℝ :=
{ x : ℝ | ∃ k : ℤ, x = (2 * k + 1) * π / 4 ∨ x = (2 * k + 1) * π / 6 }

/-
The key to solving this problem simply is that we can rewrite the equation as
a product of terms, shown in `alt_formula`, being equal to zero.
-/

def funauxiliar (x : ℝ) : ℝ := cos x * (cos x ^ 2 - 1/2) * cos (3 * x)

lemma Igualdad {x : ℝ} :
(cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 - 1) / 4 = funauxiliar x :=
begin
  rw funauxiliar,
  rw real.cos_two_mul,
  rw cos_three_mul,
  ring,
end


lemma Equivalencia {x : ℝ} : problema x ↔ funauxiliar x = 0 :=
begin
  split,
  {intro h1,
  rw problema at h1,
  rw ← Igualdad,
  rw div_eq_zero_iff,
  left,
  rw sub_eq_zero,
  exact h1,},
  {intro h2,
  rw problema,
  rw ← Igualdad at h2,
  rw div_eq_zero_iff at h2,
  norm_num at h2,
  rw sub_eq_zero at h2,
  exact h2,},
  end
  

lemma CasosSolucion {x : ℝ} :
funauxiliar x = 0 ↔ cos x ^ 2 = 1/2 ∨ cos (3 * x) = 0 :=
begin
  rw funauxiliar,
  rw mul_assoc,
  rw mul_eq_zero,
  rw mul_eq_zero,
  rw sub_eq_zero,
  split,
  {intro h1,
  cases h1 with h11 h12,
  right,
  rw cos_three_mul,
  rw h11,
  ring,
  exact h12,},
  {intro h2,
  right,
  exact h2,},
end


/-
Now we can solve for `x` using basic-ish trigonometry.
-/

lemma SolucionCosenoCuadrado {x : ℝ} : cos x ^ 2 = 1/2 ↔ 
∃ k : ℤ, x = (2 * k + 1) * π / 4 :=
begin
  rw cos_square,
  rw add_right_eq_self,
  rw div_eq_zero_iff,
  split,
  {intro h1,
  cases h1 with h11 h12,
  rw cos_eq_zero_iff at h11,
  cases h11 with k1 hk1,
  use k1,
  linarith,
  norm_num at h12,},
  {intro h2, 
  cases h2 with k2 hk2,
  left,
  rw cos_eq_zero_iff,
  use k2,
  linarith,},
end


lemma SolucionCosenoTriple {x : ℝ} : cos (3 * x) = 0 ↔ 
∃ k : ℤ, x = (2 * k + 1) * π / 6 :=
begin
  rw cos_eq_zero_iff,
  split,
  {intro h1,
  cases h1 with k1 hk1,
  use k1,
  linarith,},
  {intro h2,
  cases h2 with k2 hk2,
  use k2,
  linarith,},
end


theorem imo1962_q4 {x : ℝ} : problema x ↔ x ∈ Solucion :=
begin
  rw Equivalencia,
  rw CasosSolucion,
  rw SolucionCosenoTriple,
  rw SolucionCosenoCuadrado,
  rw Solucion,

  exact exists_or_distrib.symm,
end

