import MyNNG.Multiplication

open MyNat

theorem zero_pow_zero : (zero : MyNat) ^ zero = one := by
  rw [pow_zero]

theorem zero_pow_succ (m : MyNat) : (zero : MyNat) ^ (succ m) = zero := by
  rw [pow_succ]
  rw [mul_zero]

theorem pow_one (a : MyNat) : a ^ one = a  := by
  rw [one_eq_succ_zero]
  rw [pow_succ]
  rw [pow_zero]
  rw [one_mul]

theorem one_pow (m : MyNat) : (one : MyNat) ^ m = one := by
  induction m with
  | zero =>
    rw [pow_zero]
  | succ t ht =>
    rw [pow_succ]
    rw [ht]
    rw [one_mul]

theorem pow_two (a : MyNat) : a ^ two = a * a := by
  rw [two_eq_succ_one]
  rw [pow_succ]
  rw [pow_one]

theorem pow_add (a m n : MyNat) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero =>
    rw [add_zero]
    rw [pow_zero]
    rw [mul_one]
  | succ t ht =>
    rw [add_succ]
    rw [pow_succ]
    rw [pow_succ]
    rw [ht]
    rw [mul_assoc]

theorem mul_pow (a b n : MyNat) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero =>
    repeat rw [pow_zero]
    rw [one_mul]
  | succ t ht =>
    repeat rw [pow_succ]
    rw [ht]
    rw [mul_assoc]
    rw [mul_comm (b ^ t) (a * b)]
    rw [mul_comm (b ^ t) b]
    repeat rw [← mul_assoc]

theorem pow_pow (a m n : MyNat) : (a ^ m) ^ n = a ^ (m * n) := by
  induction n with
  | zero =>
    rw [mul_zero]
    rw [pow_zero]
    rw [pow_zero]
  | succ t ht =>
    rw [pow_succ]
    rw [ht]
    rw [mul_succ]
    rw [pow_add]

theorem add_sq (a b : MyNat) : (a + b) ^ two = a ^ two + b ^ two + two * a * b := by
  rw [pow_two, pow_two, pow_two]
  rw [add_right_comm]
  rw [mul_add, add_mul, add_mul]
  rw [two_mul, add_mul]
  rw [mul_comm b a]
  rw [← add_assoc, ← add_assoc]
