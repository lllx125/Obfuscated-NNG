import MyNNG.Header

open MyNat

theorem zero_add (n : MyNat) : .zero + n = n := by
  induction n with
  | zero =>
    rw [add_zero]
  | succ d ih =>
    rw [add_succ,ih]

theorem succ_add (a b : MyNat) : succ a + b = succ (a + b)  := by
  induction b with
  | zero =>
    rw [add_zero,add_zero]
  | succ d ih =>
    rw [add_succ,ih,add_succ]

theorem add_comm (a b : MyNat) : a + b = b + a := by
  induction b with
  | zero =>
    rw [add_zero, zero_add]
  | succ d ih =>
    rw [add_succ, ih, succ_add]

theorem add_assoc (a b c : MyNat) : a + b + c = a + (b + c) := by
  induction c with
  | zero =>
    rw [add_zero, add_zero]
  | succ d ih =>
    rw [add_succ, add_succ, ih, add_succ]

theorem add_right_comm (a b c : MyNat) : a + b + c = a + c + b := by
  rw [add_assoc]
  rw [add_comm b, add_assoc]

theorem add_left_comm (a b c : MyNat) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc]
  rw [add_comm a b]
  rw [add_assoc]

theorem succ_eq_add_one (n : MyNat) : succ n = n + one := by
  rw [one_eq_succ_zero]
  rw [add_succ, add_zero]
