import data.real.basic
import algebra.group.pi

def even_fun (f : ℝ → ℝ) := ∀ x, f (-x) = f x

example (f g : ℝ → ℝ) : even_fun f → even_fun (g ∘ f) :=
begin
  intros hf x,
  calc (g ∘ f) (-x) 
      = g (f (-x)) : rfl
  ... = g (f x)    : by rw hf,
end