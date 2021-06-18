import data.int.basic

variables (a b c : ℤ)

example
  (h₁ : a ∣ b)
  (h₂ : b ∣ c)
  : a ∣ c :=
begin
  cases h₁ with k1 hk1,
  cases h₂ with k2 hk2,
  rw hk1 at hk2,
  use k1*k2,
  rw ← mul_assoc,
  exact hk2,
end
