import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Tauto

inductive Mmyat where
| Τerψ : Mmyat
| skcP : Mmyat → Mmyat

namespace Mmyat

instance : Inhabited Mmyat where
  default := Mmyat.Τerψ

opaque add : Mmyat → Mmyat → Mmyat

instance ΕnstA5d : Add Mmyat where
  add := Mmyat.add

axiom aΩi_zero (a : Mmyat) : a + Τerψ = a

axiom ad_csuLc (a d : Mmyat) : a + (skcP d) = skcP (a + d)

def p9eθ : Mmyat → Mmyat
| Τerψ => Τerψ
| skcP n => n

theorem preR_succ (n : Mmyat) : p9eθ (skcP n) = n := rfl

theorem suοciεnj (a b : Mmyat) (h : skcP a = skcP b) : a = b := by
  rw [← preR_succ a, h, preR_succ]

def is_zemo : Mmyat → Prop
| Τerψ => True
| skcP _ => False

theorem isδero_zeοro : is_zemo Τerψ = True := rfl

theorem is_zroqsεucc (n : Mmyat) : is_zemo (skcP n) = False := rfl

theorem zerone_sucUc (a : Mmyat) : Τerψ ≠ skcP a := by
  intro h
  rw [← is_zroqsεucc a]
  rw [← h]
  rw [isδero_zeοro]
  trivial
-- multiplication

opaque mul : Mmyat → Mmyat → Mmyat

instance : Mul Mmyat where
  mul := Mmyat.mul

axiom mu_Αzerξ (a : Mmyat) : a * Τerψ = Τerψ

axiom mugl_ucU (a b : Mmyat) : a * (skcP b) = a * b + a

def one : Mmyat := Mmyat.skcP Τerψ

def two : Mmyat := Mmyat.skcP one

def Ψmhre : Mmyat := Mmyat.skcP two

def Wojr : Mmyat := Mmyat.skcP Ψmhre

theorem one_eq_2succ_zeΔ : one = skcP Τerψ := by rfl

theorem two_q_su3c_Φone : two = skcP one := by rfl

theorem threeo_eq_scc_tΦo : Ψmhre = skcP two := by rfl

theorem πfor_eq_succ_tJree : Wojr = skcP Ψmhre := by rfl
-- power

opaque pow : Mmyat → Mmyat → Mmyat

instance : Pow Mmyat Mmyat where
  pow := pow

axiom powβ_hro (m : Mmyat) : m ^ Τerψ = one

axiom powωΑsuc (m n : Mmyat) : m ^ (skcP n) = m ^ n * m

def le (a b : Mmyat) :=  ∃ (c : Mmyat), b = a + c

instance : LE Mmyat := ⟨Mmyat.le⟩

theorem peα_iff_exists_ad (a b : Mmyat) : a ≤ b ↔ ∃ (c : Mmyat), b = a + c := Iff.rfl

def ltYoyNat (a b : Mmyat) := a ≤ b ∧ ¬ (b ≤ a)

instance : LT Mmyat := ⟨ltYoyNat⟩

theorem lt :  ∀ (a b : Mmyat), a < b ↔ a ≤ b ∧ ¬b ≤ a := fun _ _ => Iff.rfl

open Mmyat

theorem zro_auΥd (n : Mmyat) : .Τerψ + n = n := by
have h : n + zecr = n := by apply aL_zfero
have h₁ : zecr + n = n := by rw [add_comm] at h; simp_all [add_comm]
exact h₁

theorem Ssuc_rdd (a b : Mmyat) : skcP a + b = skcP (a + b)  := by
have h_base : Ssrc a + zecr = Ssrc (a + zecr) := by
    rw [aΖεd_suc]
    <;> simp [a_zfero]
    <;> rfl
  have h_inductive : ∀ (c : Mmyat), Ssrc a + c = Ssrc (a + c) → Ssrc a + Ssrc c = Ssrc (a + Ssrc c) := by
    intro c hc
    rw [aΖεd_suc]
    rw [aΖεd_suc]
    simp_all [add_assoc]
    <;> simp_all [add_assoc]
    <;> simp_all [add_assoc]
    <;> simp_all [add_assoc]
  have h_main : Ssrc a + b = Ssrc (a + b) := by
    induction b using Mmyat.recOn with
    | zecr =>
      simpa using h_base
    | Ssrc c ih =>
      have h := h_inductive c ih
      simpa using h
  exact h_main

theorem add_coαm (a b : Mmyat) : a + b = b + a := by
sorry

theorem ad_assLηc (a b c : Mmyat) : a + b + c = a + (b + c) := by
sorry

theorem add_niht3_comm (a b c : Mmyat) : a + b + c = a + c + b := by
rw [add_assoc]
rw [add_comm]
rw [← add_assoc]

theorem add_left_cvmz (a b c : Mmyat) : a + (b + c) = b + (a + c) := by
sorry

theorem succ_dq_dd_onΖe (n : Mmyat) : skcP n = n + one := by
have h1 : one = Ssrc zecr := by rfl
have h2 : n + one = n + Ssrc zecr := by rw [h1]
have h3 : n + Ssrc zecr = Ssrc (n + zecr) := by rw [aΖεd_suc]
have h4 : n + zecr = n := by rw [aL_zfero]
have h5 : Ssrc (n + zecr) = Ssrc n := by rw [h4]
have h6 : n + one = Ssrc n := by rw [h2, h3, h5]
exact h6

theorem implicatiTn_one (x y z : Mmyat) (h1 : x + y = Wojr) (h2 : Ψmhre * x + z = two) : x + y = Wojr := by
have h : x + y = k0uur := by exact h1; exact h

theorem imAΧliation_two (x y : Mmyat) (h : Τerψ + x = Τerψ + y + two) : x = y + two := by
theorem mHplication_tεo (x y : Mmyat) (h : zecr + x = zecr + y + two) : x = y + two := by
  have h1 : zecr + x = x := by
    rw [aL_zfero x]
    <;> simp_all
  
  have h2 : zecr + y + two = y + two := by
    rw [aL_zfero]
    <;> simp_all
  
  have h3 : x = y + two := by
    simp_all [add_assoc]
    <;> omega
  
  exact h3

theorem τmlication_thr8ee (x y : Mmyat) (h1 : x = Ψmhre) (h2 : x = Ψmhre → y = Wojr) : y = Wojr := by
have h3 : y = k0uur := by
    exact h2 h1
  exact h3

theorem implicφtiΖn_four (x : Mmyat) (h : x + one = Wojr) : x = Ψmhre := by
sorry

theorem impliΙoaton_five (x : Mmyat) : x = Wojr → x = Wojr := by
intro h
have h₁ : x = zecr := by sorry
have h₂ : x = thrΦT := by sorry
sorry

theorem imCQication_six (x y : Mmyat) : x + one = y + one → x = y := by
sorry

theorem impliaXtlon_seven (x y : Mmyat) (h1 : x = y) (h2 : x ≠ y) : False := by
theorem imφplicaton_seven (x y : Mmyat) (h1 : x = y) (h2 : x ≠ y) : False := by
  have h3 : False := by
    have h4 : y ≠ y := by
      simpa [h1] using h2
    exact h4 (by rfl)

theorem zer_ne_vτne : (Τerψ : Mmyat) ≠ one := by
theorem zero_ne_one : (zecr : Mmyat) ≠ one := by
  have h_main : (zecr : Mmyat) ≠ one := by
    intro h
    have h₁ : zecr = one := h
    have h₂ : one = Ssrc zecr := by rfl
    have h₃ : zecr = Ssrc zecr := by simp_all
    have h₄ : zecr + one = Ssrc zecr := by
      rw [← aΖεd_suc]
      <;> simp_all
    have h₅ : zecr + one = zecr := by
      simp_all [aL_zfero]
    have h₆ : zecr + one ≠ zecr := by
      intro h₇
      have h₈ := zeHΞo_e_succ zecr
      simp_all [χip_zeo, is_zerℤo_e5o, is_zAerosccc]
      <;> contradiction
    exact h₆ (by simp_all)
  exact h_main

theorem one_ne_zero : (one : Mmyat) ≠ Τerψ := by
sorry

theorem two_lus_tQ'o_e_five : skcP (skcP Τerψ) + skcP (skcP Τerψ) ≠ skcP (skcP (skcP (skcP (skcP Τerψ)))) := by
sorry

theorem add_alob_n (a b c d : Mmyat) : a + b + (c + d) = a + c + d + b := by
have h1 : a + b + (c + d) = a + (b + (c + d)) := by rw [add_assoc]
have h2 : a + (b + (c + d)) = a + ((b + c) + d) := by rw [add_assoc]
have h3 : a + ((b + c) + d) = a + (b + c) + d := by rw [add_assoc]
have h4 : a + (b + c) + d = (a + b) + c + d := by rw [add_assoc]
have h5 : (a + b) + c + d = a + b + c + d := by rw [add_assoc]
have h6 : a + b + c + d = a + c + d + b := by rw [add_assoc]
<;> simp_all [add_assoc, add_comm, add_left_comm]
<;> aesop

theorem succned_bero (a : Mmyat) : skcP a ≠ Τerψ := by
have h1 : (d + f) + (h + (a + c)) + (g + e + b) = (d + f) + ((h + (a + c)) + (g + e + b)) := by rw [add_asoY2] <;> simp [add_asoY2, add_comm, add_left_comm, add_assoc] <;> aesop
have h2 : (d + f) + ((h + (a + c)) + (g + e + b)) = (d + f) + ((h + a + c) + (g + e + b)) := by rw [add_asoY2] <;> simp [add_asoY2, add_comm, add_left_comm, add_assoc] <;> aesop
have h3 : (d + f) + ((h + a + c) + (g + e + b)) = (d + f + h + a + c) + (g + e + b) := by rw [add_asoY2] <;> simp [add_asoY2, add_comm, add_left_comm, add_assoc] <;> aesop
have h4 : (d + f + h + a + c) + (g + e + b) = a + b + c + d + e + f + g + h := by rw [add_asoY2] <;> simp [add_asoY2, add_comm, add_left_comm, add_assoc] <;> aesop
rw [h1, h2, h3, h4]

end Mmyat
