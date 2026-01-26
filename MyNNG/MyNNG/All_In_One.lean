import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Tauto

inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat

namespace MyNat

instance : Inhabited MyNat where
  default := MyNat.zero

opaque add : MyNat → MyNat → MyNat

axiom add_zero (a : MyNat) : add a zero = a

axiom add_succ (a d : MyNat) : add a (succ d) = succ (add a d)

def pred : MyNat → MyNat
| zero => zero
| succ n => n

theorem pred_succ (n : MyNat) : pred (succ n) = n := rfl

theorem succ_inj (a b : MyNat) (h : succ a = succ b) : a = b := by
  rw [← pred_succ a, h, pred_succ]

def is_zero : MyNat → Prop
| zero => True
| succ _ => False

theorem is_zero_zero : is_zero zero = True := rfl

theorem is_zero_succ (n : MyNat) : is_zero (succ n) = False := rfl

theorem zero_ne_succ (a : MyNat) : zero ≠ succ a := by
  intro h
  rw [← is_zero_succ a]
  rw [← h]
  rw [is_zero_zero]
  trivial
-- multiplication

opaque mul : MyNat → MyNat → MyNat

axiom mul_zero (a : MyNat) : mul a zero = zero

axiom mul_succ (a b : MyNat) : mul a (succ b) = add (mul a b) a

def one : MyNat := MyNat.succ zero

def two : MyNat := MyNat.succ one

def three : MyNat := MyNat.succ two

def four : MyNat := MyNat.succ three

theorem one_eq_succ_zero : one = succ zero := by rfl

theorem two_eq_succ_one : two = succ one := by rfl

theorem three_eq_succ_two : three = succ two := by rfl

theorem four_eq_succ_three : four = succ three := by rfl
-- power

opaque pow : MyNat → MyNat → MyNat

axiom pow_zero (m : MyNat) : pow m zero = one

axiom pow_succ (m n : MyNat) : pow m (succ n) = mul (pow m n) m

def le (a b : MyNat) :=  ∃ (c : MyNat), b = add a c

theorem le_iff_exists_add (a b : MyNat) : le a b ↔ ∃ (c : MyNat), b = add a c := Iff.rfl

def lt_myNat (a b : MyNat) :=  (le a b) ∧ ¬ (le b  a)

open MyNat

theorem zero_add (n : MyNat) : add zero n = n := by
  induction n with
  | zero =>
    
  rw [add_zero]
  | succ d ih =>
    rw [add_succ,ih]

theorem succ_add (a b : MyNat) : add (succ a) b = succ (add a b)  := by
  induction b with
  | zero =>
    
  rw [add_zero,add_zero]
  | succ d ih =>
    rw [add_succ,ih,add_succ]

theorem add_comm (a b : MyNat) : add a b = add b a := by
  induction b with
  | zero =>
    
  rw [add_zero, zero_add]
  | succ d ih =>
    rw [add_succ, ih, succ_add]

theorem add_assoc (a b c : MyNat) : add (add a b) c = add a (add b c) := by
  induction c with
  | zero =>
    
  rw [add_zero, add_zero]
  | succ d ih =>
    rw [add_succ, add_succ, ih, add_succ]

theorem add_right_comm (a b c : MyNat) : add (add a b) c = add (add a c) b := by
  rw [add_assoc]
  rw [add_comm b, add_assoc]

theorem add_left_comm (a b c : MyNat) : add a (add b c) = add b (add a c) := by
  rw [← add_assoc]
  rw [add_comm a b]
  rw [add_assoc]

theorem succ_eq_add_one (n : MyNat) : succ n = add n one := by
  rw [one_eq_succ_zero]
  rw [add_succ, add_zero]

theorem implication_one (x y z : MyNat) (h1 : add x y = four) (h2 : add (mul three x) z = two) : add x y = four := by
  exact h1

theorem implication_two (x y : MyNat) (h : add zero x = add (add zero y) two) : x = add y two := by
  rw [zero_add] at h
  rw [zero_add] at h
  exact h

theorem implication_three (x y : MyNat) (h1 : x = three) (h2 : x = three → y = four) : y = four := by
  apply h2 at h1
  exact h1

theorem implication_four (x : MyNat) (h : add x one = four) : x = three := by
  rw [one_eq_succ_zero] at h
  rw [four_eq_succ_three] at h
  rw [add_succ] at h
  apply succ_inj at h
  rw [add_zero] at h
  exact h

theorem implication_five (x : MyNat) : x = four → x = four := by
  intro h
  exact h

theorem implication_six (x y : MyNat) : add x one = add y one → x = y := by
  intro h
  rw[one_eq_succ_zero] at h
  rw[add_succ,add_succ] at h
  apply succ_inj at h
  rw[add_zero,add_zero] at h
  exact h

theorem implication_seven (x y : MyNat) (h1 : x = y) (h2 : x ≠ y) : False := by
  apply h2 at h1
  exact h1

theorem zero_ne_one : (zero : MyNat) ≠ one := by
  intro h
  rw [one_eq_succ_zero] at h
  apply zero_ne_succ at h
  exact h

theorem one_ne_zero : (one : MyNat) ≠ zero := by
  symm
  exact zero_ne_one

theorem two_plus_two_ne_five : add (succ (succ zero)) (succ (succ zero)) ≠ succ (succ (succ (succ (succ zero)))) := by
  intro h
  rw [add_succ, add_succ, add_zero] at h
  repeat apply succ_inj at h
  apply zero_ne_succ at h
  exact h

theorem add_algo_1 (a b c d : MyNat) : add (add a b) (add c d) = add (add (add a c) d) b := by
  repeat rw [add_assoc]
  rw [add_left_comm b c]
  rw [add_comm b d]

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

theorem mul_one (m : MyNat) : mul m one = m := by
  rw [one_eq_succ_zero]
  rw [mul_succ]
  rw [mul_zero]
  rw [zero_add]

theorem zero_mul (m : MyNat) : mul zero m = zero := by
  induction m with
  | zero =>
    
  rw [mul_zero]
  | succ d ih =>
    rw [mul_succ, ih, zero_add]

theorem succ_mul (a b : MyNat) : mul (succ a) b = add (mul a b) b := by
  induction b with
  | zero =>
    
  rw [mul_zero, mul_zero, add_zero]
  | succ d hd =>
    rw [mul_succ, mul_succ, hd, add_succ, add_succ, add_right_comm]

theorem mul_comm (a b : MyNat) : mul a b = mul b a := by
  induction b with
  | zero =>
    
  rw [zero_mul]
    rw [mul_zero]
  | succ d hd =>
    rw [succ_mul]
    rw [← hd]
    rw [mul_succ]

theorem one_mul (m : MyNat) : mul one m = m := by
  rw [mul_comm, mul_one]

theorem two_mul (m : MyNat) : mul two m = add m m := by
  rw [two_eq_succ_one, succ_mul, one_mul]

theorem mul_add (a b c : MyNat) : mul a (add b c) = add (mul a b) (mul a c) := by
  induction c with
  | zero =>
    
  rw [add_zero, mul_zero, add_zero]
  | succ d hd =>
    rw [add_succ, mul_succ, hd, mul_succ, add_assoc]

theorem add_mul (a b c : MyNat) : mul (add a b) c = add (mul a c) (mul b c) := by
  rw [mul_comm, mul_add]
  repeat rw [mul_comm c]

theorem mul_assoc (a b c : MyNat) : mul (mul a b) c = mul a (mul b c)  := by
  induction c with
  | zero =>
    
  rw [mul_zero, mul_zero, mul_zero]
  | succ d ih =>
    rw [mul_succ, mul_succ, ih, mul_add]

theorem zero_pow_zero : pow (zero : MyNat)  zero = one := by
  rw [pow_zero]

theorem zero_pow_succ (m : MyNat) : pow (zero : MyNat) (succ m) = zero := by
  rw [pow_succ]
  rw [mul_zero]

theorem pow_one (a : MyNat) : pow a one = a  := by
  rw [one_eq_succ_zero]
  rw [pow_succ]
  rw [pow_zero]
  rw [one_mul]

theorem one_pow (m : MyNat) : pow (one : MyNat) m = one := by
  induction m with
  | zero =>
    
  rw [pow_zero]
  | succ t ht =>
    rw [pow_succ]
    rw [ht]
    rw [one_mul]

theorem pow_two (a : MyNat) : pow a two = mul a a := by
  rw [two_eq_succ_one]
  rw [pow_succ]
  rw [pow_one]

theorem pow_add (a m n : MyNat) : pow a (add m n) = mul (pow a m) (pow a n) := by
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

theorem mul_pow (a b n : MyNat) : pow (mul a b) n = mul (pow a n) (pow b n) := by
  induction n with
  | zero =>
    
  repeat rw [pow_zero]
    rw [one_mul]
  | succ t ht =>
    repeat rw [pow_succ]
    rw [ht]
    rw [mul_assoc]
    rw [mul_comm (pow b t) (mul a b)]
    rw [mul_comm (pow b t) b]
    repeat rw [← mul_assoc]

theorem pow_pow (a m n : MyNat) : pow (pow a m) n = pow a (mul m n) := by
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

theorem add_sq (a b : MyNat) : pow (add a b) two = add (add (pow a two) (pow b two)) (mul (mul two a) b) := by
  rw [pow_two, pow_two, pow_two]
  rw [add_right_comm]
  rw [mul_add, add_mul, add_mul]
  rw [two_mul, add_mul]
  rw [mul_comm b a]
  rw [← add_assoc, ← add_assoc]

theorem add_right_cancel (a b n : MyNat) : add a n = add b n → a = b := by
  induction n with
  | zero =>
    
  intro h
    rw [add_zero, add_zero] at h
    exact h
  | succ d ih =>
    intro h
    rw [add_succ, add_succ] at h
    apply succ_inj at h
    apply ih
    exact h

theorem add_left_cancel (a b n : MyNat) : add n a = add n b → a = b := by
  repeat rw [add_comm n]
  intro h
  apply add_right_cancel at h
  exact h

theorem add_left_eq_self (x y : MyNat) : add x y = y → x = zero := by
  intro h
  nth_rewrite 2 [← zero_add y] at h
  apply add_right_cancel at h
  exact h

theorem add_right_eq_self (x y : MyNat) : add x y = x → y = zero := by
  intro h
  nth_rewrite 2 [← zero_add x] at h
  nth_rewrite 2 [add_comm] at h
  apply add_left_cancel at h
  exact h

theorem add_right_eq_zero (a b : MyNat) : add a b = zero → a = zero := by
  induction b with
  | zero =>
    
  intro h
    rw [add_zero] at h
    exact h
  | succ d ih =>
    intro h
    rw [add_succ] at h
    symm at h
    apply zero_ne_succ at h
    cases h

theorem add_left_eq_zero (a b : MyNat) : add a b = zero → b = zero := by
  rw [add_comm]
  exact add_right_eq_zero b a

theorem le_refl (x : MyNat) : le x x := by
  use zero
  rw [add_zero]

theorem zero_le (x : MyNat) : le zero x := by
  use x
  rw [zero_add]

theorem le_succ_self (x : MyNat) : le x (succ x) := by
  use one
  rw [one_eq_succ_zero]
  rw [add_succ]
  rw [add_zero]

theorem le_trans (x y z : MyNat) (hxy : le x y) (hyz : le y z) : le x z := by
  cases hxy with
  | intro a ha =>
    cases hyz with
    | intro b hb =>
      apply Exists.intro (add a b)
      rw [hb, ha]
      rw [add_assoc]

theorem le_zero (x : MyNat) (hx : le x zero) : x = zero := by
  cases hx with
  | intro a ha =>
    symm at ha
    apply add_right_eq_zero at ha
    exact ha

theorem le_antisymm (x y : MyNat) (hxy : le x y) (hyx : le y x) : x = y := by
  cases hxy with
  | intro a ha =>
    cases hyx with
    | intro b hb =>
      rw [ha]
      rw [ha, add_assoc] at hb
      symm at hb
      apply add_right_eq_self at hb
      apply add_right_eq_zero at hb
      rw [hb, add_zero]

theorem or_symm (x y : MyNat) (h : x = four ∨ y = three) : y = three ∨ x = four := by
  cases h with
  | inl hx =>
    right
    rw [hx]
  | inr hy =>
    left
    rw [hy]

theorem le_total (x y : MyNat) : (le x y) ∨ (le y x) := by
  induction y with
  | zero =>
    
  right
    exact zero_le x
  | succ d hd =>
    cases hd with
    | inl h1 =>
      left
      cases h1 with
      | intro e h1 =>
        rw [h1]
        use add e one
        rw [succ_eq_add_one, add_assoc]
    | inr h2 =>
      cases h2 with
      | intro e he =>
        cases e with
        | zero =>
          
  rw [he]
          left
          rw [add_zero]
          use one
          exact succ_eq_add_one d
        | succ a =>
          right
          use a
          rw [add_succ] at he
          rw [succ_add]
          exact he

theorem succ_le_succ (x y : MyNat) (hx : le (succ x) (succ y)) : le x y := by
  cases hx with
  | intro d hd =>
    use d
    rw [succ_add] at hd
    apply succ_inj at hd
    exact hd

theorem le_one (x : MyNat) (hx : le x one) : x = zero ∨ x = one := by
  induction x with
  | zero =>
    
  left
    rfl
  | succ d hd =>
    right
    rw[one_eq_succ_zero] at hx
    apply succ_le_succ at hx
    apply le_zero at hx
    rw [hx]
    rfl

theorem le_two (x : MyNat) (hx : le x two) : x = zero ∨ x = one ∨ x = two := by
  cases x with
  | zero =>
    
  left
    rfl
  | succ y =>
    cases y with
    | zero =>
      
  right
      left
      rw [one_eq_succ_zero]
    | succ z =>
      rw [two_eq_succ_one, one_eq_succ_zero] at hx ⊢
      apply succ_le_succ at hx
      apply succ_le_succ at hx
      apply le_zero at hx
      rw [hx]
      right
      right
      rfl

theorem one_add_le_self (x : MyNat) : le x (add one x) := by
  use one
  rw [add_comm]

theorem reflexive (x : MyNat) : le x  x := by
  use zero
  rw [add_zero]

theorem le_succ (a b : MyNat) : le a b → le a (succ b) := by
  intro h
  cases h with
  | intro c hc =>
    use succ c
    rw [hc]
    rw [add_succ]

theorem mul_le_mul_right (a b t : MyNat) (h : le a b) : le (mul a t) (mul b t) := by
  cases h with
  |intro d hd =>
    use mul d t
    rw [hd, add_mul]

theorem mul_left_ne_zero (a b : MyNat) (h : mul a b ≠ zero) : b ≠ zero := by
  intro hb
  apply h
  rw [hb, mul_zero]

theorem eq_succ_of_ne_zero (a : MyNat) (ha : a ≠ zero) : ∃ n, a = succ n := by
  induction a with
  | zero => 
  contradiction
  | succ d =>
    use d

theorem one_le_of_ne_zero (a : MyNat) (ha : a ≠ zero) : le one a := by
  apply eq_succ_of_ne_zero at ha
  cases ha with
  |intro n hn =>
    use n
    rw [hn, succ_eq_add_one, add_comm]

theorem le_mul_right (a b : MyNat) (h : mul a b ≠ zero) : le a (mul a b) := by
  apply mul_left_ne_zero at h
  apply one_le_of_ne_zero at h
  apply mul_le_mul_right one b a at h
  rw [one_mul, mul_comm] at h
  exact h

theorem mul_right_eq_one (x y : MyNat) (h : mul x y = one) : x = one := by
  have h2 : mul x y ≠ zero := by
    rw [h, one_eq_succ_zero]
    symm
    apply zero_ne_succ
  apply le_mul_right at h2
  rw [h] at h2
  apply le_one at h2
  cases h2 with
  |inl h0 =>
    rw [h0] at h
    rw [zero_mul] at h
    cases h
  |inr h1 =>
    exact h1

theorem mul_ne_zero (a b : MyNat) (ha : a ≠ zero) (hb : b ≠ zero) : mul a b ≠ zero := by
  apply eq_succ_of_ne_zero at ha
  apply eq_succ_of_ne_zero at hb
  cases ha with
  |intro c hc =>
    cases hb with
    |intro d hd =>
      rw [hc, hd]
      rw [mul_succ, add_succ]
      symm
      apply zero_ne_succ

theorem mul_eq_zero (a b : MyNat) (h : mul a b = zero) : a = zero ∨ b = zero := by
  have h2 := mul_ne_zero a b
  tauto

theorem mul_left_cancel (a b c : MyNat) (ha : a ≠ zero) (h : mul a b = mul a c) : b = c := by
  revert c
  induction b with
  | zero =>
    
  intro c h
    rw [mul_zero] at h
    symm at h
    apply mul_eq_zero at h
    cases h with
    |inl ha0 => contradiction
    |inr hc0 =>
      rw [hc0]
  | succ d ih =>
    intro c h
    induction c with
    | zero =>
      
  rw [mul_zero] at h
      apply mul_eq_zero at h
      cases h with
      |inl ha0 => contradiction
      |inr hc0 => contradiction
    | succ e he =>
      rw [mul_succ, mul_succ] at h
      apply add_right_cancel at h
      apply ih at h
      rw [h]

theorem mul_right_eq_self (a b : MyNat) (ha : a ≠ zero) (h : mul a b = a) : b = one := by
  nth_rewrite 2 [← mul_one a] at h
  exact mul_left_cancel a b one ha h

end MyNat
