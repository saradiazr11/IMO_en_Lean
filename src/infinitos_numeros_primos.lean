import data.nat.factorial
import data.nat.prime

open nat

theorem infinitos_numeros_primos :
  ∀ n, ∃ p ≥ n, prime p:=
begin
  intro n,

  let m:= factorial n + 1,
  let p:= min_fac m,
  have hp: prime p :=
  begin
    refine min_fac_prime _,
    sorry,
  end,

  use p,
  split,
  { by_contradiction,
    have h1: p ∣ factorial n + 1 := min_fac_dvd m,
    have h2: p ∣ factorial n := by sorry,
    have h3: p ∣ 1 := (nat.dvd_add_right h2).mp h1,
    exact prime.not_dvd_one hp h3,},
  { exact hp, },
end

lemma h2
  (n : ℕ)
  (m : ℕ)
  (p : ℕ)
  (m = n.factorial + 1)
  (p = m.min_fac)
  (hp : prime p)
  (h : ¬p ≥ n)
  (h1 : p ∣ n.factorial + 1)
  : p ∣ factorial n:=
begin
  refine hp.dvd_factorial.mpr _,
  exact le_of_not_ge h,
end

lemma hp
  (n : ℕ)
  (m = n.factorial + 1)
  (p = m.min_fac)
  : prime p:=
begin
  sorry,
end
