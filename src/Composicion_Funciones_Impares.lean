import data.real.basic

def odd_fun (f : ℝ → ℝ) := ∀ x, f (-x) = -f x

example (f g : ℝ → ℝ) : odd_fun f → odd_fun g →  odd_fun (g ∘ f) :=
begin
  intros hf hg x,
  calc (g ∘ f) (-x)
      = g (f (-x)) : rfl
  ... = g (-f x)   : by rw hf
  ... =-g (f x)    : by rw hg
  ... = -(g ∘ f) x : rfl,
end
