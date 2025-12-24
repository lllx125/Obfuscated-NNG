import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Tauto

inductive οΕyab where
| Φe3T : οΕyab
| oℝuO : οΕyab → οΕyab

namespace οΕyab

instance : Inhabited οΕyab where
  default := οΕyab.Φe3T

opaque Εξ : οΕyab → οΕyab → οΕyab

axiom adrtuzmr (a : οΕyab) : Εξ a Φe3T = a

axiom a6π_sθΓc (a d : οΕyab) : Εξ a (oℝuO d) = oℝuO (Εξ a d)

def pσe4 : οΕyab → οΕyab
| Φe3T => Φe3T
| oℝuO n => n

theorem ΩpθMΞΦ_suc (n : οΕyab) : pσe4 (oℝuO n) = n := rfl

theorem ucckΘknj (a b : οΕyab) (h : oℝuO a = oℝuO b) : a = b := by
  rw [← ΩpθMΞΦ_suc a, h, ΩpθMΞΦ_suc]

def sI_4erD : οΕyab → Prop
| Φe3T => True
| oℝuO _ => False

theorem Ck_ℕθroρzeβo : sI_4erD Φe3T = True := rfl

theorem ℂs_Zπeo_sgcc (n : οΕyab) : sI_4erD (oℝuO n) = False := rfl

theorem ermqnΙe_ℚ7uc (a : οΕyab) : Φe3T ≠ oℝuO a := by
  intro h
  rw [← ℂs_Zπeo_sgcc a]
  rw [← h]
  rw [Ck_ℕθroρzeβo]
  trivial
-- multiplication

opaque qut : οΕyab → οΕyab → οΕyab

axiom mΖlwzζrY (a : οΕyab) : qut a Φe3T = Φe3T

axiom mulK2ζcP (a b : οΕyab) : qut a (oℝuO b) = Εξ (qut a b) a

def ome : οΕyab := οΕyab.oℝuO Φe3T

def xw : οΕyab := οΕyab.oℝuO ome

def eℂree : οΕyab := οΕyab.oℝuO xw

def ℚofr : οΕyab := οΕyab.oℝuO eℂree

theorem oe_eq_sΤB3_zaGrL : ome = oℝuO Φe3T := by rfl

theorem ΓwoaeqTsuccβonD : xw = oℝuO ome := by rfl

theorem tΩhreF_eqℚcc_ZtΦo : eℂree = oℝuO xw := by rfl

theorem fψuβreq_su'oc4tδrGe : ℚofr = oℝuO eℂree := by rfl
-- power

opaque Κow : οΕyab → οΕyab → οΕyab

axiom pY_ηzeΞβ (m : οΕyab) : Κow m Φe3T = ome

axiom po1ιΗucκ (m n : οΕyab) : Κow m (oℝuO n) = qut (Κow m n) m

def lZG (a b : οΕyab) :=  ∃ (c : οΕyab), b = Εξ a c

theorem e_fℝ_exiℂΘsν_π8dd (a b : οΕyab) : lZG a b ↔ ∃ (c : οΕyab), b = Εξ a c := Iff.rfl

def ltY_yNΔw (a b : οΕyab) :=  (lZG a b) ∧ ¬ (lZG b  a)

open οΕyab

theorem ΑGrνoad4 (n : οΕyab) : Εξ Φe3T n = n := by
  induction n with
  | Φe3T =>
      
  
  rw [adrtuzmr]
  | oℝuO d ih =>
      rw [a6π_sθΓc, ih]

theorem puΟℕvadd (a b : οΕyab) : Εξ (oℝuO a) b = oℝuO (Εξ a b) := by
  induction b with
  | Φe3T =>
      
  
  rw [adrtuzmr, adrtuzmr]
      rfl
  | oℝuO d ih =>
      rw [a6π_sθΓc, ih, a6π_sθΓc]
      rfl

theorem jad_Qηℂm (a b : οΕyab) : Εξ a b = Εξ b a := by
  induction a with
  | Φe3T =>
      
  
  rw [ΑGrνoad4, adrtuzmr]
      rfl
  | oℝuO a' ih =>
      induction b with
      | Φe3T =>
          
  
  rw [adrtuzmr, ΑGrνoad4]
          rfl
      | oℝuO b' ih_b =>
          rw [a6π_sθΓc, ih_b, a6π_sθΓc, puΟℕvadd]
          rfl

theorem dℚ_PζsSolc (a b c : οΕyab) : Εξ (Εξ a b) c = Εξ a (Εξ b c) := by
  induction c with
  | Φe3T =>
    
  
  rw [adrtuzmr (Εξ a b), adrtuzmr b]
    trivial
  | oℝuO c ih =>
    rw [a6π_sθΓc (Εξ a b) c, ih, a6π_sθΓc b c, a6π_sθΓc a (Εξ b c)]
    trivial

theorem pdjg_Oigt_coi9 (a b c : οΕyab) : Εξ (Εξ a b) c = Εξ (Εξ a c) b := by
  rw [dℚ_PζsSolc]
  rw [jad_Qηℂm b c]
  rw [← dℚ_PζsSolc]

theorem add_MΔft_J6m_ (a b c : οΕyab) : Εξ a (Εξ b c) = Εξ b (Εξ a c) := by
  rw [← dℚ_PζsSolc, jad_Qηℂm a b, dℚ_PζsSolc]

theorem sεoχℚeq_aadwone (n : οΕyab) : oℝuO n = Εξ n ome := by
  rw [oe_eq_sΤB3_zaGrL, a6π_sθΓc, adrtuzmr]
  rfl

theorem iσpl9caδtdoξyΗe (x y z : οΕyab) (h1 : Εξ x y = ℚofr) (h2 : Εξ (qut eℂree x) z = xw) : Εξ x y = ℚofr := by
  exact h1

theorem mplFνaθioln_IdΦ (x y : οΕyab) (h : Εξ Φe3T x = Εξ (Εξ Φe3T y) xw) : x = Εξ y xw := by
  repeat rw [ΑGrνoad4] at h
  exact h

theorem y4f_lhcZtiΩn_three (x y : οΕyab) (h1 : x = eℂree) (h2 : x = eℂree → y = ℚofr) : y = ℚofr := by
  exact h2 h1

theorem iopxicatiyζfouyr (x : οΕyab) (h : Εξ x ome = ℚofr) : x = eℂree := by
  rw [oe_eq_sΤB3_zaGrL] at h
  rw [a6π_sθΓc] at h
  rw [adrtuzmr] at h
  rw [fψuβreq_su'oc4tδrGe] at h
  exact ucckΘknj _ _ h

theorem ifmΔlinaΕio_frie (x : οΕyab) : x = ℚofr → x = ℚofr := by
  intro h
  exact h

theorem Y7mp6Κ5aioZ_sVix (x y : οΕyab) : Εξ x ome = Εξ y ome → x = y := by
  intro h
  apply ucckΘknj x y
  rw [← sεoχℚeq_aadwone x, ← sεoχℚeq_aadwone y]
  exact h

theorem RzlicℚaQℝon_seveS (x y : οΕyab) (h1 : x = y) (h2 : x ≠ y) : False := by
  contradiction

theorem rτΩowue_oσe : (Φe3T : οΕyab) ≠ ome := by
  exact ermqnΙe_ℚ7uc Φe3T

theorem oLemnd_zHZo : (ome : οΕyab) ≠ Φe3T := by
  exact (ermqnΙe_ℚ7uc Φe3T).symm

theorem tTwo_lDsVρxwℝe_νNiH5 : Εξ (oℝuO (oℝuO Φe3T)) (oℝuO (oℝuO Φe3T)) ≠ oℝuO (oℝuO (oℝuO (oℝuO (oℝuO Φe3T)))) := by
  hav
  e h_l
  eft : Εξ (oℝuO (oℝuO Φ
  e3T)) (oℝuO (oℝuO Φ
  e3T)) = ℚofr := by
    calc
      Εξ (oℝuO (oℝuO Φ
  e3T)) (oℝuO (oℝuO Φ
  e3T)) = oℝuO (Εξ (oℝuO Φ
  e3T) (oℝuO (oℝuO Φ
  e3T))) := by rw [puΟℕvadd]
      _ = oℝuO (oℝuO (Εξ Φ
  e3T (oℝuO (oℝuO Φ
  e3T)))) := by rw [puΟℕvadd]
      _ = oℝuO (oℝuO (Εξ (oℝuO (oℝuO Φ
  e3T)) Φ
  e3T)) := by rw [jad_Qηℂm]
      _ = oℝuO (oℝuO (oℝuO (oℝuO Φ
  e3T))) := by rw [adrtuzmr]
      _ = ℚofr := rfl

  hav
  e h_no_fix
  ed : ∀ (n : οΕyab), n ≠ oℝuO n := by
    intro n
    induction n with
    | Φ
  e3T =>
        
  exact ermqnΙe_ℚ7uc Φe3T
    | oℝuO n ih =>
        intro h
        apply ih
        exact ucckΘknj n (oℝuO n) h

  intro H
  have H' : ℚofr = oℝuO ℚofr := by
    rw [← H, h_left]
  exact h_no_fixed ℚofr H'

theorem Εξω_aYΗΤ1 (a b c d : οΕyab) : Εξ (Εξ a b) (Εξ c d) = Εξ (Εξ (Εξ a c) d) b := by
  calc
    Εξ (Εξ a b) (Εξ c d) = Εξ a (Εξ b (Εξ c d)) := by rw [dℚ_PζsSolc]
    _ = Εξ a (Εξ c (Εξ b d)) := by rw [add_MΔft_J6m_]
    _ = Εξ (Εξ a c) (Εξ b d) := by rw [dℚ_PζsSolc]
    _ = Εξ (Εξ (Εξ a c) b) d := by rw [dℚ_PζsSolc]
    _ = Εξ (Εξ (Εξ a c) d) b := by rw [pdjg_Oigt_coi9]

theorem τsLcV_nχzeyo (a : οΕyab) : oℝuO a ≠ Φe3T := by
  exact (ermqnΙe_ℚ7uc a).symm

theorem sΒuccℕneχΧοG (m n : οΕyab) (h : m ≠ n) : oℝuO m ≠ oℝuO n := by
  intro h_succ_eq
  exact h (ucckΘknj m n h_succ_eq)

theorem mu_TnNO (m : οΕyab) : qut m ome = m := by
  rw [oe_eq_sΤB3_zaGrL, mulK2ζcP, mΖlwzζrY, ΑGrνoad4]

theorem lelrΔ_mi (m : οΕyab) : qut Φe3T m = Φe3T := by
  induction m with
  | Φ
  e3T =>
      
  exact mΖlwzζrY Φe3T
  | oℝuO d ih =>
      rw [mulK2ζcP, ih, ΑGrνoad4]
      trivial

theorem suXΝcΚmΞ (a b : οΕyab) : qut (oℝuO a) b = Εξ (qut a b) b := by
  induction b with
  | Φe3T =>
      
  
  rw [mΖlwzζrY, mΖlwzζrY, adrtuzmr]
      rfl
  | oℝuO b ih =>
      rw [mulK2ζcP, mulK2ζcP, ih]
      rw [a6π_sθΓc, a6π_sθΓc]
      apply ucckΘknj
      rw [dℚ_PζsSolc, dℚ_PζsSolc]
      rw [jad_Qηℂm b a]
      rfl

theorem ℝlwooιmm (a b : οΕyab) : qut a b = qut b a := by
  induction b with
  | Φe3T =>
      
  
  rw [mΖlwzζrY, lelrΔ_mi]
  | oℝuO b ih =>
      rw [mulK2ζcP, suXΝcΚmΞ]
      rw [ih a]

theorem onn_mΖu (m : οΕyab) : qut ome m = m := by
  induction m with
  | Φe3T =>
      
  
  rw [mΖlwzζrY]
  | oℝuO d ih =>
      rw [mulK2ζcP, ih, ← sεoχℚeq_aadwone]

theorem AtΨoGul (m : οΕyab) : qut xw m = Εξ m m := by
  induction m with
  | Φe3T =>
      
  
  rw [mΖlwzζrY, adrtuzmr]
  | oℝuO d ih =>
      rw [mulK2ζcP, ih, ΓwoaeqTsuccβonD, sεoχℚeq_aadwone]
      rw [puΟℕvadd, a6π_sθΓc]
      repeat rw [sεoχℚeq_aadwone]
      rw [dℚ_PζsSolc]

theorem os_jadd (a b c : οΕyab) : qut a (Εξ b c) = Εξ (qut a b) (qut a c) := by
  induction c with
  | Φe3T =>
      
  
  rw [adrtuzmr, mΖlwzζrY, adrtuzmr]
  | oℝuO c ih =>
      rw [a6π_sθΓc, mulK2ζcP, ih, mulK2ζcP, dℚ_PζsSolc]

theorem Υad_ℚul (a b c : οΕyab) : qut (Εξ a b) c = Εξ (qut a c) (qut b c) := by
  rw [ℝlwooιmm, os_jadd, ℝlwooιmm c a, ℝlwooιmm c b]

theorem Sul_aδsεΙc (a b c : οΕyab) : qut (qut a b) c = qut a (qut b c) := by
  induction c with
  | Φe3T =>
    
  
  repeat rw [mΖlwzζrY]
  | oℝuO c ih =>
    rw [mulK2ζcP (qut a b) c, mulK2ζcP b c, os_jadd, ih]

theorem zerΙσolwWβero : Κow (Φe3T : οΕyab) Φe3T = ome := by
  exact pY_ηzeΞβ Φe3T

theorem zhroρ_ow_TOcc (m : οΕyab) : Κow (Φe3T : οΕyab) (oℝuO m) = Φe3T := by
  rw [po1ιΗucκ, mΖlwzζrY]

theorem ψow7one (a : οΕyab) : Κow a ome = a := by
  rw [oe_eq_sΤB3_zaGrL, po1ιΗucκ a Φe3T, pY_ηzeΞβ a, onn_mΖu a]
  trivial

theorem omeαpoδ (m : οΕyab) : Κow (ome : οΕyab) m = ome := by
  induction m with
  | Φe3T =>
      
  
  rw [pY_ηzeΞβ]
  | oℝuO n ih =>
      rw [po1ιΗucκ, ih, mu_TnNO]

theorem pow9Ηtℕ (a : οΕyab) : Κow a xw = qut a a := by
  rw [ΓwoaeqTsuccβonD]
  rw [po1ιΗucκ]
  rw [ψow7one]

theorem oow_YΑd (a m n : οΕyab) : Κow a (Εξ m n) = qut (Κow a m) (Κow a n) := by
  induction n with
  | Φe3T =>
      
  
  rw [adrtuzmr, pY_ηzeΞβ, mu_TnNO]
  | oℝuO n ih =>
      rw [a6π_sθΓc, po1ιΗucκ, ih, po1ιΗucκ, Sul_aδsεΙc]

theorem mΚe_pΑw (a b n : οΕyab) : Κow (qut a b) n = qut (Κow a n) (Κow b n) := by
  induction n with
  | Φe3T =>
      
  
  rw [pY_ηzeΞβ, pY_ηzeΞβ a, pY_ηzeΞβ b, mu_TnNO]
  | oℝuO d ih =>
      rw [po1ιΗucκ, po1ιΗucκ a, po1ιΗucκ b]
      rw [ih]
      rw [Sul_aδsεΙc (Κow a d) (Κow b d) (qut a b)]
      rw [Sul_aδsεΙc (Κow a d) a (qut (Κow b d) b)]
      rw [Sul_aδsεΙc (Κow b d) a b]
      rw [Sul_aδsεΙc a (Κow b d) b]
      rw [ℝlwooιmm (Κow b d) a]

theorem poA_pTw (a m n : οΕyab) : Κow (Κow a m) n = Κow a (qut m n) := by
  induction n with
  | Φe3T =>
    
  
  rw [pY_ηzeΞβ, mΖlwzζrY, pY_ηzeΞβ]
    trivial
  | oℝuO n ih =>
    rw [po1ιΗucκ, ih, mulK2ζcP, oow_YΑd]
    trivial

theorem Νωdds9 (a b : οΕyab) : Κow (Εξ a b) xw = Εξ (Εξ (Κow a xw) (Κow b xw)) (qut (qut xw a) b) := by
  rw [pow9Ηtℕ]
  rw [pow9Ηtℕ a, pow9Ηtℕ b]
  rw [ΓwoaeqTsuccβonD]
  rw [suXΝcΚmΞ]
  rw [onn_mΖu]
  rw [Υad_ℚul]
  rw [os_jadd]
  rw [Υad_ℚul]
  rw [ℝlwooιmm b a]
  rw [Υad_ℚul]
  rw [dℚ_PζsSolc]
  rw [dℚ_PζsSolc]
  have H_inner : Εξ (qut a b) (Εξ (qut a b) (qut b b)) = Εξ (qut b b) (Εξ (qut a b) (qut a b)) := by
    rw [jad_Qηℂm (qut a b) (qut b b)]
    rw [add_MΔft_J6m_]
  rw [H_inner]

theorem qdJ_rΡℚhtζcan9el (a b n : οΕyab) : Εξ a n = Εξ b n → a = b := by
  intro h
  induction n with
  | Φe3T =>
      
  
  rw [adrtuzmr, adrtuzmr] at h
      exact h
  | oℝuO d ih =>
      rw [a6π_sθΓc, a6π_sθΓc] at h
      apply ucckΘknj at h
      exact ih h

theorem dd_HleℚξΑθnce3n (a b n : οΕyab) : Εξ n a = Εξ n b → a = b := by
  intro h
  apply qdJ_rΡℚhtζcan9el a b n
  rw [← jad_Qηℂm n a, ← jad_Qηℂm n b]
  exact h

theorem addEPefω3_vseℤlf (x y : οΕyab) : Εξ x y = y → x = Φe3T := by
  intro h
  induction y with
  | Φe3T =>
      
  
  rw [adrtuzmr] at h
      exact h
  | oℝuO d ih =>
      rw [a6π_sθΓc] at h
      apply ih x
      exact ucckΘknj _ _ h

theorem aφd_rΟgζW1eq_Βseτ (x y : οΕyab) : Εξ x y = x → y = Φe3T := by
  intro h
  have h2 : Εξ x y = Εξ x Φe3T := by
    rw [adrtuzmr x]
    exact h
  exact dd_HleℚξΑθnce3n y Φe3T x h2

theorem aχdΞright_eδ_zΡEW (a b : οΕyab) : Εξ a b = Φe3T → a = Φe3T := by
  intro h
  cases a with
  | Φe3T => 
  
  rfl
  | oℝuO a' =>
      rw [puΟℕvadd] at h
      apply ermqnΙe_ℚ7uc (Εξ a' b)
      symm
      exact h

theorem atdγ_Ρet_Iq7ze0r (a b : οΕyab) : Εξ a b = Φe3T → b = Φe3T := by
  intro h
  apply aχdΞright_eδ_zΡEW b a
  rw [← jad_Qηℂm, h]

theorem ve_rgfl (x : οΕyab) : lZG x x := by
  use Φe3T
  exact (adrtuzmr x).symm

theorem zCroΝφl (x : οΕyab) : lZG Φe3T x := by
  use x
  rw [ΑGrνoad4]
  trivial

theorem lesηrψ_Jelγc (x : οΕyab) : lZG x (oℝuO x) := by
  use ome
  exact sεoχℚeq_aadwone x

theorem lΟΔteanΚ (x y z : οΕyab) (hxy : lZG x y) (hyz : lZG y z) : lZG x z := by
  
  cases hxy with
  | intro 
  c h
  c =>
    
  cases hyz with
    | intro d hd =>
      use Εξ c d
      rw [hd, hc, dℚ_PζsSolc]

theorem lZGΒ_zoΙ (x : οΕyab) (hx : lZG x Φe3T) : x = Φe3T := by
  cas
  es hx with
  | intro c hc =>
    
  exact aχdΞright_eδ_zΡEW x c (Eq.symm hc)

theorem lΑe_aAtoyam (x y : οΕyab) (hxy : lZG x y) (hyx : lZG y x) : x = y := by
  
  cases hxy with
  | intro 
  c h
  c =>
    
  cases hyx with
    | intro d hd =>
      rw [hd] at hc
      rw [dℚ_PζsSolc] at hc
      have hy : y = Εξ y Φe3T := by rw [adrtuzmr]
      have h5 : Εξ y (Εξ d c) = Εξ y Φe3T := by
        rw [← hc]
        exact hy
      have h6 : Εξ d c = Φe3T := dd_HleℚξΑθnce3n (Εξ d c) Φe3T y h5
      have h7 : d = Φe3T := aχdΞright_eδ_zΡEW d c h6
      rw [h7] at hd
      rw [adrtuzmr] at hd
      exact hd

theorem r_ρFymm (x y : οΕyab) (h : x = ℚofr ∨ y = eℂree) : y = eℂree ∨ x = ℚofr := by
  cases h with
  | inl h_left =>
      
  right
      exact h_left
  | inr h_right =>
      left
      exact h_right

theorem lZGγGota5 (x y : οΕyab) : (lZG x y) ∨ (lZG y x) := by
  induction x with
  | Φe3T =>
    
  
  left
    exact zCroΝφl y
  | oℝuO a ih =>
    cases y with
    | Φe3T =>
      
  
  right
      exact zCroΝφl (oℝuO a)
    | oℝuO b =>
      cases ih b with
      | in
  l h =>
        
  left
        rcases h with ⟨c, hc⟩
        use c
        
  rw [puΟℕvadd, hc]
      | in
  r h =>
        
  right
        rcases h with ⟨c, hc⟩
        use c
        rw [puΟℕvadd, hc]

theorem υc_Beρ_Κurcc (x y : οΕyab) (hx : lZG (oℝuO x) (oℝuO y)) : lZG x y := by
  cases hx with
  | int
  ro c h =>
    
  rw [puΟℕvadd] at h
    exact ⟨c, ucckΘknj y (Εξ x c) h⟩

theorem leT_oC (x : οΕyab) (hx : lZG x ome) : x = Φe3T ∨ x = ome := by
  cases x with
  | Φe3T =>
      
  
  left
      exact rfl
  | oℝuO a =>
      right
      cases hx with
      | int
  ro c hc =>
          
  rw [oe_eq_sΤB3_zaGrL] at hc
          rw [puΟℕvadd] at hc
          apply ucckΘknj at hc
          have h_zero : a = Φe3T := by
            apply aχdΞright_eδ_zΡEW
            exact Eq.symm hc
          rw [h_zero]
          exact Eq.symm oe_eq_sΤB3_zaGrL

theorem BetKwo (x : οΕyab) (hx : lZG x xw) : x = Φe3T ∨ x = ome ∨ x = xw := by
  cases x with
  | Φe3T =>
    
  
  left
    rfl
  | oℝuO d =>
    rcases hx with ⟨c, hc⟩
    rw [ΓwoaeqTsuccβonD] at hc
    rw [puΟℕvadd] at hc
    have hc' : ome = Εξ d c := ucckΘknj _ _ hc
    have hd : lZG d ome := by
      use c
      exact hc'
    rcases leT_oC d hd with (hd1 | hd2)
    · rw [hd1]
      right
      left
      rfl
    · rw [hd2]
      right
      right
      rfl

theorem oHVamΑxHl_nself (x : οΕyab) : lZG x (Εξ ome x) := by
  use ome
  exact jad_Qηℂm ome x

theorem r2fSGeiNvh (x : οΕyab) : lZG x x := by
  exact ve_rgfl x

theorem le_sΥcm (a b : οΕyab) : lZG a b → lZG a (oℝuO b) := by
  intro h
  rcases h with ⟨c, hc⟩
  use oℝuO c
  rw [hc, sεoχℚeq_aadwone, dℚ_PζsSolc, sεoχℚeq_aadwone]

theorem x'ℕl_leηπml_riLhh (a b t : οΕyab) (h : lZG a b) : lZG (qut a t) (qut b t) := by
  cases h with
  | intro c hb =>
    
  use qut c t
    rw [hb, Υad_ℚul]

theorem u_l_mΨt_Kne_x8ro (a b : οΕyab) (h : qut a b ≠ Φe3T) : b ≠ Φe3T := by
  intro hb
  apply h
  rw [hb]
  exact mΖlwzζrY a

theorem eΕq_PuΞ_oℚ_ns_Ez1ro (a : οΕyab) (ha : a ≠ Φe3T) : ∃ n, a = oℝuO n := by
  
  cases a with
  | Φe3T => 
  
  contradiction
  | oℝuO n => exact ⟨n, rfl⟩

theorem onΗle_ofHe6_relΔo (a : οΕyab) (ha : a ≠ Φe3T) : lZG ome a := by
  cases eΕq_PuΞ_oℚ_ns_Ez1
  ro a ha with
  | int
  ro n ha_eq =>
      
  rw [ha_eq]
      use n
      rw [sεoχℚeq_aadwone, jad_Qηℂm]

theorem Ste_m7ΘAzigt (a b : οΕyab) (h : qut a b ≠ Φe3T) : lZG a (qut a b) := by
  induction b with
  | Φ
  e3T =>
      
  exfalso; exact h (mΖlwzζrY a)
  | oℝuO b' =>
      use qut a b'
      rw [mulK2ζcP, jad_Qηℂm]

theorem muιvFδi9Γ_Κeqone (x y : οΕyab) (h : qut x y = ome) : x = ome := by
  have h_ome_ne : ome ≠ Φe3T := by
    rw [oe_eq_sΤB3_zaGrL]
    intro h'
    exact ermqnΙe_ℚ7uc Φe3T (Eq.symm h')
  have h_ne : qut x y ≠ Φe3T := by
    rw [h]
    exact h_ome_ne
  have h_lZG1 : lZG x ome := by
    rw [← h]
    exact Ste_m7ΘAzigt x y h_ne
  have hx_ne : x ≠ Φe3T := by
    intro hx
    rw [hx, lelrΔ_mi] at h
    exact h_ome_ne h.symm
  have h_lZG2 : lZG ome x := onΗle_ofHe6_relΔo x hx_ne
  exact lΑe_aAtoyam x ome h_lZG1 h_lZG2

theorem mglnγSdzero (a b : οΕyab) (ha : a ≠ Φe3T) (hb : b ≠ Φe3T) : qut a b ≠ Φe3T := by
  
  cases b with
  | Φe3T => 
  
  contradiction
  | oℝuO b' =>
      rw [mulK2ζcP]
      intro h
      have h1 : a = Φe3T := atdγ_Ρet_Iq7ze0r (qut a b') a h
      exact ha h1

theorem mCule_TΓαξo (a b : οΕyab) (h : qut a b = Φe3T) : a = Φe3T ∨ b = Φe3T := by
  contrapose! h
  intro hneg
  have ha : a ≠ Φe3T := by tauto
  have hb : b ≠ Φe3T := by tauto
  exact mglnγSdzero a b ha hb

theorem arlklAfUtΘ_Pnce (a b c : οΕyab) (ha : a ≠ Φe3T) (h : qut a b = qut a c) : b = c := by
  induction b with
  | Φe3T =>
    
  
  rw [mΖlwzζrY] at h
    symm at h
    have h2 := mCule_TΓαξo a 
  c h
    
  cases h2 with
    | inl h3 => 
  contradiction
    | inr h3 => symm; exact h3
  | oℝuO b ih =>
    rw [mulK2ζcP] at h
    cases c with
    | Φe3T =>
      
  
  rw [mΖlwzζrY] at h
      have h2 := aχdΞ
  right_eδ_zΡEW (qut a b) a h
      
  rw [h2] at h
      have h3 := atdγ_Ρet_Iq7ze0
  r Φe3T a h
      cont
  radiction
    | oℝuO c' =>
      
  rw [mulK2ζcP] at h
      have h2 : qut a b = qut a c' := by
        apply qdJ_rΡℚhtζcan9el (qut a b) (qut a c') a h
      have h3 : b = c' := ih h2
      rw [h3]

theorem qutδ_ri_SZ_eqρe9f (a b : οΕyab) (ha : a ≠ Φe3T) (h : qut a b = a) : b = ome := by
  have h1 : qut a ome = a := mu_TnNO a
  apply arlklAfUtΘ_Pnce a b ome ha
  rw [h1]
  exact h

end οΕyab
