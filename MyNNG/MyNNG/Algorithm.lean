import MyNNG.Addition

open MyNat

theorem add_algo_1 (a b c d : MyNat) : a + b + (c + d) = a + c + d + b := by
  repeat rw [add_assoc]
  rw [add_left_comm b c]
  rw [add_comm b d]

theorem add_algo_2 (a b c d e f g h : MyNat) : (d + f) + (h + (a + c)) + (g + e + b) = a + b + c + d + e + f + g + h := by
  simp only [add_left_comm, add_comm]

theorem succ_ne_zero (a : MyNat) : succ a ≠ zero := by
  intro h
  rw [← is_zero_succ a]
  rw [h]
  rw [is_zero_zero]
  trivial

theorem succ_ne_succ (m n : MyNat) (h : m ≠ n) : succ m ≠ succ n := by
  contrapose! h
  apply succ_inj at h
  exact h
