import data.real.basic

def even_fun (f : ℝ → ℝ) := ∀ x, f (-x) = f x

example (
  f g : ℝ → ℝ)
  : even_fun f → even_fun g →  even_fun (f + g) :=
begin
  intros hf hg,
  intros x,
  calc (f + g) (-x) = f (-x) + g (-x) : rfl
                ... = f x + g (-x)    : by rw hf
                ... = f x + g x       : by rw hg
                ... = (f + g) x       : rfl,
end
