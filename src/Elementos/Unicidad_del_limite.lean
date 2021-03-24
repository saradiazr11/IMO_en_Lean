import data.real.basic

variables (u : ℕ → ℝ)
variables (a b x y : ℝ)

notation `|`x`|` := abs x

def limite : (ℕ → ℝ) → ℝ → Prop :=
λ u c, ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - c| ≤ ε

lemma eq_of_abs_sub_le_all
  : (∀ ε > 0, |x - y| ≤ ε) → x = y :=
begin
  intro h,
  apply eq_of_abs_sub_nonpos,
  by_contradiction H,
  push_neg at H,
  specialize h ( |x-y|/2) (by linarith),
  linarith,
end

example
  (ha : limite u a)
  (hb : limite u b)
  : a = b :=
begin
  apply eq_of_abs_sub_le_all,
  intros eps eps_pos,
  cases ha (eps/2) (by linarith) with N1 hN1,
  cases hb (eps/2) (by linarith) with N2 hN2,
  let N0:=max N1 N2,
  calc  |a-b|
      = |(a-u N0)+(u N0-b)| : by ring_nf
  ... ≤ |a-u N0| + |u N0-b| : by apply abs_add
  ... = |u N0-a| + |u N0-b| : by rw abs_sub
  ... ≤ eps                 : by linarith [hN1 N0 (le_max_left N1 N2),
                                           hN2 N0 (le_max_right N1 N2)],
end
