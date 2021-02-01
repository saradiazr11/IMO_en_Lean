import tuto_lib
variables {u v: ℕ → ℝ} {l l' : ℝ}
example (hu : seq_limit u l) (hv : seq_limit v l') :
seq_limit (u + v) (l + l') :=
begin
  intros eps eps_pos,
  cases hu (eps/2) (by linarith) with N1 hN1,
  cases hv (eps/2) (by linarith) with N2 hN2,
  let N0:= max N1 N2,
  use N0,
  intros n hn,
  rw ge_max_iff at hn,
  calc
  |(u + v) n - (l + l')| = |u n + v n - (l + l')|   : rfl
                     ... = |(u n - l) + (v n - l')| : by congr' 1 ; ring
                     ... ≤ |u n - l| + |v n - l'|   : by apply abs_add
                     ... ≤  eps                     : by linarith [hN1 n (by linarith), hN2 n (by linarith)],
end