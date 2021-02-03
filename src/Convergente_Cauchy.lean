import data.real.basic

variables {u : ℕ → ℝ} {a l : ℝ}

notation `|`x`|` := abs x

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

def cauchy_sequence (u : ℕ → ℝ) := ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

example : (∃ l, seq_limit u l) → cauchy_sequence u :=
begin
  intros h eps eps_pos,
  cases h with l hl,
  rw seq_limit at hl,
  cases hl (eps/2) (by linarith) with N hN,
  use N,
  intros p q hp hq,
  calc |u p - u q| = |(u p - l)+(l - u q)| : by ring
              ... ≤ |u p - l| + |l - u q|  : by apply abs_add
              ... = |u p - l| + |u q - l|  : by rw abs_sub l (u q)
              ... ≤ eps/2 + eps/2          : by linarith [hN p hp, hN q hq]
              ... = eps                    : by ring,
end