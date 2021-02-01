import data.real.basic
import data.int.parity
variables (a b c : ℤ)
example (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b+c :=
begin
  cases h1 with k1 hk1,
  rw hk1,
  cases h2 with k2 hk2,
  rw hk2,
  use k1+k2,
  ring,
end