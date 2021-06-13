/-
 Ejemplos de las diversas tácticas usadas en el desarrollo del TFM.
 -/

 /-
 TÁCTICA SORRY
 -/
import data.real.basic
import data.int.parity
variables (a b c : ℤ)

example (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c :=
begin
  sorry,
end

/-
TÁCTICA SORRY Y HAVE
-/

example (a b : ℝ) : a = a*b → a = 0 ∨ b = 1 :=
begin
  intro hyp,
  have H : a*(1 - b) = 0, by sorry,
  sorry,
end

/-
TÁCTICA REWRITE
-/

example (a b : ℝ) : (a + b)*(a - b) = a^2 - b^2 :=
begin
  rw mul_sub (a+b) a b,
  rw add_mul a b b,
  rw pow_two a,
  rw pow_two b,
  rw mul_comm a b,
  rw ← sub_sub ((a+b)*a) (b*a) (b*b),
  rw add_mul a b a,
  rw ← add_sub,
  rw sub_self,
  rw add_zero (a*a), 
end

/-
TÁCTICAS REWRITE Y EXACT
-/

example (a b c d : ℝ) (hyp : c = d*a + b) (hyp' : b = a*d) : c = 2*a*d :=
begin
  rw hyp' at hyp,
  rw mul_comm d a at hyp,
  rw ← two_mul (a*d) at hyp,
  rw ← mul_assoc 2 a d at hyp,
  exact hyp,
end

/-
TÁCTICA LINARITH
-/
def up_bounds (A : set ℝ) := { x : ℝ | ∀ a ∈ A, a ≤ x}
def is_max (a : ℝ) (A : set ℝ) := a ∈ A ∧ a ∈ up_bounds A
infix ` is_a_max_of `:55 := is_max

example (A : set ℝ) (x y : ℝ) (hx : x is_a_max_of A) (hy : y is_a_max_of A) : 
x = y :=
begin
  have : x ≤ y, from hy.2 x hx.1,
  have : y ≤ x, from hx.2 y hy.1,
  linarith,
end

/-
TÁCTICA NLINARITH
-/



/-
TÁCTICA APPLY
-/
def non_decreasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂
def non_increasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≥ f x₂

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_increasing g) : 
non_increasing (g ∘ f) :=
begin
  intros x1 x2 h,
  apply hg,
  apply hf,
  exact h,
end

/-
TÁCTICA RING
-/

example (a b : ℝ) : (a + b) + a = 2*a + b :=
begin
  by ring,
end

