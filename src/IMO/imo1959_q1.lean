import tactic.ring
import data.nat.prime

open nat

lemma Auxiliar
  (n k : ℕ)
  (h1 : k ∣ 21 * n + 4)
  (h2 : k ∣ 14 * n + 3)
  : k ∣ 1 :=
begin
  have h3 : k ∣ 2 * (21 * n + 4),
    from dvd_mul_of_dvd_right h1 2,
  have h4 : k ∣ 3 * (14 * n + 3),
    from dvd_mul_of_dvd_right h2 3,
  have h5 : 3 * (14 * n + 3) = 2 * (21 * n + 4) + 1,
    { ring, },
  rw h5 at h4,
  rw ← nat.dvd_add_right h3,
  exact h4,
end

theorem imo1959_q1 :
  ∀ n : ℕ, coprime (21 * n + 4) (14 * n + 3) :=
begin
  intro n,
  apply coprime_of_dvd',
  intros k hk h1 h2,
  exact Auxiliar n k h1 h2,
end
