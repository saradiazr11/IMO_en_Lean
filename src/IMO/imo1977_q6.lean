import data.pnat.basic

-- El enunciado del IMO 1977 Q6 es el siguiente:
--    Sea `f : ℕ+ → ℕ+` tal que `f(f(n)) < f(n + 1)` para todo
--    `n`. Demostrar que `f(n) = n` para todo `n`.

theorem imo1977_q6_nat2
  (f : ℕ → ℕ)
  (h1 : ∀ n, f (f n) < f (n + 1))
  : ∀ n, f n = n :=
begin
  have h2: ∀ (k n : ℕ), k ≤ n → k ≤ f n,
  { intro k,
     induction k with k h_ind,
     { intros n hn,
       exact nat.zero_le (f n), },
     { intros n hk,
       apply nat.succ_le_of_lt,
       rw nat.succ_eq_add_one at hk,
       have hk1: k ≤ n-1 := nat.le_sub_right_of_add_le hk,
       have hk2: k ≤ f (n-1):= h_ind (n-1) hk1,
       have hk3: k ≤ f(f(n-1)) := h_ind (f(n-1)) hk2,
       have h11: f (f (n-1)) < f(n-1+1):= h1 (n-1),
       rw nat.sub_add_cancel at h11,
       { calc k ≤ f(f(n-1)) : hk3
            ... < f(n)      : h11,},
       have hk0: 1 ≤ k+1 := nat.succ_le_succ (nat.zero_le k),
       exact (le_trans hk0 hk), }},
  have hf: ∀ n, n ≤ f n,
    { intro n,
      apply h2 n n,
      exact le_rfl, },
  have mon: ∀ n, f n < f(n+1),
    { intro n,
      exact lt_of_le_of_lt (hf (f n)) (h1 n), },
  have f_mon: strict_mono f := strict_mono.nat mon,
  intro n,
  apply nat.eq_of_le_of_lt_succ (hf n),
  exact (f_mon.lt_iff_lt.mp (h1 n)),
end

theorem imo1977_q62
  (f : ℕ+ → ℕ+)
  (h : ∀ n, f (f n) < f (n + 1))
  : ∀ n, f n = n :=
begin
  intro n,
  simpa using imo1977_q6_nat2 (λ m, if 0 < m then f m.to_pnat' else 0) _ n,
  intro x,
  cases x,
  { simp },
  { simpa using h _},
end
