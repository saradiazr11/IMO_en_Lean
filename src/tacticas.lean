/-
 Ejemplos de las diversas tácticas usadas en el desarrollo del TFM.
 -/

 /-
 TÁCTICA SORRY
 -/
import data.real.basic
import data.int.parity
import algebra.group.pi
import data.nat.prime
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
TÁCTICAS INTRO e INTROS
-/
example (a b : ℝ): 0 ≤ b → a ≤ a + b :=
begin
  intro hb,
  exact le_add_of_nonneg_right hb,
end

example (P Q : Prop) (h₁ : P ∨ Q) (h₂ : ¬ (P ∧ Q)) : Q → ¬P :=
begin
  intros q p,
  exact h₂ ⟨ p,q⟩ ,
end

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
TÁCTICA LINARITH
-/
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a + b :=
begin
  linarith,
end

/-
TÁCTICA NLINARITH
-/
example (a b c d : ℤ)
  (hba : b < a)
  (hcb : c < b)
  (hdc : d < c)
  (h : a*c + b*d = (a + b - c + d) * (-a + b + c + d))
  : a*c + b*d < a*b + c*d:=
begin
  nlinarith,
end

/-
TÁCTICA ASSUME
-/
variables{n : ℕ}
example : ∀ n, 3*n=n*3 :=
begin
  assume n,
  sorry,
end

/-
TÁCTICA BY_CONTRADICTION
-/

example (P Q : Prop) (h : ¬ Q → ¬ P) : P → Q :=
begin
  intro hP,
  by_contradiction hnQ,
  exact h hnQ hP,
end


/-
TÁCTICA LET
-/
variables (u v w : ℕ → ℝ) (l l' : ℝ)
notation `|`x`|` := abs x
def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

def tendsto_infinity (u : ℕ → ℝ) := ∀ A, ∃ N, ∀ n ≥ N, u n ≥ A

example {u : ℕ → ℝ} : tendsto_infinity u → ∀ l, ¬ seq_limit u l :=
begin
  intro h,
  intro l,
  intro lim,
  cases lim 1 (by linarith) with N1 hN1,
  cases h (l+2) with N2 hN2,
  let N3:= max N1 N2,
  sorry,
end



/-
TÁCTICA USE
-/

example : ∃ n : ℕ, 8 = 2*n :=
begin
  use 4,
  refl, 
end

/-
TÁCTICA INDUCTION
-/

example (t a b : ℕ) : t * (a + b) = t * a + t * b :=
begin
induction b with k h,
{sorry,},

{sorry,},
end



/-
TÁCTICA CASES
-/
example {a b : ℝ} : (0 ≤ a ∧ 0 ≤ b) → 0 ≤ a + b :=
begin
  intros hyp,
  cases hyp with ha hb,
  exact add_nonneg ha hb,
end

example (a b : ℝ) : a = a*b → a = 0 ∨ b = 1 :=
begin
  intro hyp,
  have H : a*(1 - b) = 0,
  { calc a*(1 - b) = a - a*b : by ring
               ... = 0       : by linarith, },
  rw mul_eq_zero at H,
  cases H with Ha Hb,
  { sorry, },
  { sorry, },
end

/-
TÁCTICA SPLIT
-/
example (P Q R : Prop) : (P ∧ Q → R) ↔ (P → (Q → R)) :=
begin
  split, 
  {intros h1 h2 h3,
  exact h1 ⟨ h2,h3⟩ },
  {intros h1 h2,
  cases h2 with p q,
  exact h1 p q}
end

example (P Q : Prop) (hp: P) (hq : Q) : P ∧ Q :=
begin
  split, 
  {exact hp,},
  {exact hq,},
end


/-
TÁCTICA FROM
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
TÁCTICA LEFT RIGHT
-/
example (a b : ℝ) : a = a*b → a = 0 ∨ b = 1 :=
begin
  intro hyp,
  have H : a*(1 - b) = 0,
  { calc a*(1 - b) = a - a*b : by ring
               ... = 0       : by linarith, },
  rw mul_eq_zero at H,
  cases H with Ha Hb,
  { left,
    exact Ha, },
  { right,
    linarith, },
end


/-
TÁCTICA LIBRARY SEARCH
-/
example (a b : ℝ): 0 ≤ a → b ≤ a + b :=
begin
  library_search,
end

example (a b : ℝ): 0 ≤ a → b ≤ a + b :=
begin
  exact le_add_of_nonneg_left,
end


/-
TÁCTICA NORM NUM
-/

example : (2 : ℝ) + 2 = 4 := 
begin
  norm_num,
end

example : (73 : ℝ) < 789/2 := 
begin
  norm_num,
end


/-
TÁCTICA REFINE
-/
example (p : ℕ) (h: p.prime) : 1 ∣ p :=
begin
  refine is_unit.dvd _,
  exact is_unit_one,
end



/-
TÁCTICA RING
-/

example (a b : ℝ) : (a + b) + a = 2*a + b :=
begin
  by ring,
end



/-
TÁCTICA SIMP
-/
example (a b : ℝ) (h : b=0): a + b = a :=
begin
  simp,
  exact h,
end

/-
TÁCTICA SIMPA
-/
example (a b : ℝ) (h : b=0): a + b = a :=
begin
  simpa,
end


/-
TÁCTICA SUGGEST
-/

example (a b : ℕ) : a + b ≤ a + b +1 :=
begin
  suggest,
  sorry,
end 

example (a b : ℕ) : a + b ≤ a + b +1 :=
begin
  exact (a + b).le_succ,
end 

example (a b : ℕ) : a + b ≤ a + b +1 :=
begin
  exact nat.le.intro rfl,
end 
