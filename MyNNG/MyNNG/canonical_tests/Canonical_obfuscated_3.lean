import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Tauto
import Canonical

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

-- Theorem 1: ΑGrνoad4
theorem ΑGrνoad4 (n : οΕyab) : Εξ Φe3T n = n := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 2: puΟℕvadd
theorem puΟℕvadd (a b : οΕyab) : Εξ (oℝuO a) b = oℝuO (Εξ a b)  := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, a6π_sθΓc, adrtuzmr]

-- Theorem 3: jad_Qηℂm
theorem jad_Qηℂm (a b : οΕyab) : Εξ a b = Εξ b a := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 4: dℚ_PζsSolc
theorem dℚ_PζsSolc (a b c : οΕyab) : Εξ (Εξ a b) c = Εξ a (Εξ b c) := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 5: pdjg_Oigt_coi9
theorem pdjg_Oigt_coi9 (a b c : οΕyab) : Εξ (Εξ a b) c = Εξ (Εξ a c) b := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 6: add_MΔft_J6m_
theorem add_MΔft_J6m_ (a b c : οΕyab) : Εξ a (Εξ b c) = Εξ b (Εξ a c) := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, a6π_sθΓc, adrtuzmr]

-- Theorem 7: sεoχℚeq_aadwone
theorem sεoχℚeq_aadwone (n : οΕyab) : oℝuO n = Εξ n ome := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 8: iσpl9caδtdoξyΗe
theorem iσpl9caδtdoξyΗe (x y z : οΕyab) (h1 : Εξ x y = ℚofr) (h2 : Εξ (qut eℂree x) z = xw) : Εξ x y = ℚofr := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 9: mplFνaθioln_IdΦ
theorem mplFνaθioln_IdΦ (x y : οΕyab) (h : Εξ Φe3T x = Εξ (Εξ Φe3T y) xw) : x = Εξ y xw := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 10: y4f_lhcZtiΩn_three
theorem y4f_lhcZtiΩn_three (x y : οΕyab) (h1 : x = eℂree) (h2 : x = eℂree → y = ℚofr) : y = ℚofr := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 11: iopxicatiyζfouyr
theorem iopxicatiyζfouyr (x : οΕyab) (h : Εξ x ome = ℚofr) : x = eℂree := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 12: ifmΔlinaΕio_frie
theorem ifmΔlinaΕio_frie (x : οΕyab) : x = ℚofr → x = ℚofr := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 13: Y7mp6Κ5aioZ_sVix
theorem Y7mp6Κ5aioZ_sVix (x y : οΕyab) : Εξ x ome = Εξ y ome → x = y := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 14: RzlicℚaQℝon_seveS
theorem RzlicℚaQℝon_seveS (x y : οΕyab) (h1 : x = y) (h2 : x ≠ y) : False := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, False.rec, ermqnΙe_ℚ7uc]

-- Theorem 15: rτΩowue_oσe
theorem rτΩowue_oσe : (Φe3T : οΕyab) ≠ ome := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, False.rec, ermqnΙe_ℚ7uc]

-- Theorem 16: oLemnd_zHZo
theorem oLemnd_zHZo : (ome : οΕyab) ≠ Φe3T := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, False.rec, ermqnΙe_ℚ7uc]

-- Theorem 17: tTwo_lDsVρtwoℝe_νNiH5
theorem tTwo_lDsVρxwℝe_νNiH5 : Εξ (oℝuO (oℝuO Φe3T)) (oℝuO (oℝuO Φe3T)) ≠ oℝuO (oℝuO (oℝuO (oℝuO (oℝuO Φe3T)))) := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, False.rec, ermqnΙe_ℚ7uc]

-- Theorem 18: addω_aYΗΤ1
theorem Εξω_aYΗΤ1 (a b c d : οΕyab) : Εξ (Εξ a b) (Εξ c d) = Εξ (Εξ (Εξ a c) d) b := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 19: τsLcV_nχzeyo
theorem τsLcV_nχzeyo (a : οΕyab) : oℝuO a ≠ Φe3T := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, False.rec, ermqnΙe_ℚ7uc]

-- Theorem 20: sΒuccℕneχΧοG
theorem sΒuccℕneχΧοG (m n : οΕyab) (h : m ≠ n) : oℝuO m ≠ oℝuO n := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, False.rec, ermqnΙe_ℚ7uc]

-- Theorem 21: mu_TnNO
theorem mu_TnNO (m : οΕyab) : qut m ome = m := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 22: lelrΔ_mi
theorem lelrΔ_mi (m : οΕyab) : qut Φe3T m = Φe3T := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 23: suXΝcΚmΞ
theorem suXΝcΚmΞ (a b : οΕyab) : qut (oℝuO a) b = Εξ (qut a b) b := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 24: ℝlwooιmm
theorem ℝlwooιmm (a b : οΕyab) : qut a b = qut b a := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 25: onn_mΖu
theorem onn_mΖu (m : οΕyab) : qut ome m = m := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 26: AtΨoGul
theorem AtΨoGul (m : οΕyab) : qut xw m = Εξ m m := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 27: os_jadd
theorem os_jadd (a b c : οΕyab) : qut a (Εξ b c) = Εξ (qut a b) (qut a c) := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, a6π_sθΓc, adrtuzmr]

-- Theorem 28: Υad_ℚul
theorem Υad_ℚul (a b c : οΕyab) : qut (Εξ a b) c = Εξ (qut a c) (qut b c) := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 29: Sul_aδsεΙc
theorem Sul_aδsεΙc (a b c : οΕyab) : qut (qut a b) c = qut a (qut b c)  := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 30: zerΙσolwWβero
theorem zerΙσolwWβero : Κow (Φe3T : οΕyab)  Φe3T = ome := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 31: zhroρ_ow_TOcc
theorem zhroρ_ow_TOcc (m : οΕyab) : Κow (Φe3T : οΕyab) (oℝuO m) = Φe3T := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 32: ψow7one
theorem ψow7one (a : οΕyab) : Κow a ome = a  := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 33: oneαpoδ
theorem omeαpoδ (m : οΕyab) : Κow (ome : οΕyab) m = ome := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 34: pow9Ηtℕ
theorem pow9Ηtℕ (a : οΕyab) : Κow a xw = qut a a := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, po1ιΗucκ, pY_ηzeΞβ]

-- Theorem 35: oow_YΑd
theorem oow_YΑd (a m n : οΕyab) : Κow a (Εξ m n) = qut (Κow a m) (Κow a n) := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 36: mΚe_pΑw
theorem mΚe_pΑw (a b n : οΕyab) : Κow (qut a b) n = qut (Κow a n) (Κow b n) := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 37: poA_pTw
theorem poA_pTw (a m n : οΕyab) : Κow (Κow a m) n = Κow a (qut m n) := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 38: Νωdds9
theorem Νωdds9 (a b : οΕyab) : Κow (Εξ a b) xw = Εξ (Εξ (Κow a xw) (Κow b xw)) (qut (qut xw a) b) := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 39: qdJ_rΡℚhtζcan9el
theorem qdJ_rΡℚhtζcan9el (a b n : οΕyab) : Εξ a n = Εξ b n → a = b := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 40: dd_HleℚξΑθnce3n
theorem dd_HleℚξΑθnce3n (a b n : οΕyab) : Εξ n a = Εξ n b → a = b := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 41: addEPefω3_vseℤlf
theorem addEPefω3_vseℤlf (x y : οΕyab) : Εξ x y = y → x = Φe3T := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, a6π_sθΓc, adrtuzmr]

-- Theorem 42: aφd_rΟgζW1eq_Βseτ
theorem aφd_rΟgζW1eq_Βseτ (x y : οΕyab) : Εξ x y = x → y = Φe3T := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 43: aχdΞright_eδ_zΡEW
theorem aχdΞright_eδ_zΡEW (a b : οΕyab) : Εξ a b = Φe3T → a = Φe3T := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 44: atdγ_Ρet_Iq7ze0r
theorem atdγ_Ρet_Iq7ze0r (a b : οΕyab) : Εξ a b = Φe3T → b = Φe3T := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 45: ve_rgfl
theorem ve_rgfl (x : οΕyab) : lZG x x := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 46: zCroΝφl
theorem zCroΝφl (x : οΕyab) : lZG Φe3T x := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 47: lesηrψ_Jelγc
theorem lesηrψ_Jelγc (x : οΕyab) : lZG x (oℝuO x) := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 48: lΟΔteanΚ
theorem lΟΔteanΚ (x y z : οΕyab) (hxy : lZG x y) (hyz : lZG y z) : lZG x z := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 49: leΒ_zoΙ
theorem lZGΒ_zoΙ (x : οΕyab) (hx : lZG x Φe3T) : x = Φe3T := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 50: lΑe_aAtoyam
theorem lΑe_aAtoyam (x y : οΕyab) (hxy : lZG x y) (hyx : lZG y x) : x = y := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 51: r_ρFymm
theorem r_ρFymm (x y : οΕyab) (h : x = ℚofr ∨ y = eℂree) : y = eℂree ∨ x = ℚofr := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, Or.inl, Or.inr, Or.elim]

-- Theorem 52: leγGota5
theorem lZGγGota5 (x y : οΕyab) : (lZG x y) ∨ (lZG y x) := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, Or.inl, Or.inr, Or.elim]

-- Theorem 53: υc_Beρ_Κurcc
theorem υc_Beρ_Κurcc (x y : οΕyab) (hx : lZG (oℝuO x) (oℝuO y)) : lZG x y := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 54: leT_oC
theorem leT_oC (x : οΕyab) (hx : lZG x ome) : x = Φe3T ∨ x = ome := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, Or.inl, Or.inr, Or.elim]

-- Theorem 55: BetKwo
theorem BetKwo (x : οΕyab) (hx : lZG x xw) : x = Φe3T ∨ x = ome ∨ x = xw := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, Or.inl, Or.inr, Or.elim]

-- Theorem 56: oHVamΑxHl_nself
theorem oHVamΑxHl_nself (x : οΕyab) : lZG x (Εξ ome x) := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 57: r2fSGeiNvh
theorem r2fSGeiNvh (x : οΕyab) : lZG x  x := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 58: le_sΥcm
theorem le_sΥcm (a b : οΕyab) : lZG a b → lZG a (oℝuO b) := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 59: x'ℕl_leηπml_riLhh
theorem x'ℕl_leηπml_riLhh (a b t : οΕyab) (h : lZG a b) : lZG (qut a t) (qut b t) := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 60: u_l_mΨt_Kne_x8ro
theorem u_l_mΨt_Kne_x8ro (a b : οΕyab) (h : qut a b ≠ Φe3T) : b ≠ Φe3T := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, False.rec, ermqnΙe_ℚ7uc]

-- Theorem 61: eΕq_PuΞ_oℚ_ns_Ez1ro
theorem eΕq_PuΞ_oℚ_ns_Ez1ro (a : οΕyab) (ha : a ≠ Φe3T) : ∃ n, a = oℝuO n := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, False.rec, ermqnΙe_ℚ7uc, Exists.intro, Exists.elim]

-- Theorem 62: onΗle_ofHe6_relΔo
theorem onΗle_ofHe6_relΔo (a : οΕyab) (ha : a ≠ Φe3T) : lZG ome a := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, False.rec, ermqnΙe_ℚ7uc]

-- Theorem 63: Ste_m7ΘAzigt
theorem Ste_m7ΘAzigt (a b : οΕyab) (h : qut a b ≠ Φe3T) : lZG a (qut a b) := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, False.rec, ermqnΙe_ℚ7uc]

-- Theorem 64: muιvFδi9Γ_Κeqone
theorem muιvFδi9Γ_Κeqone (x y : οΕyab) (h : qut x y = ome) : x = ome := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj]

-- Theorem 65: mglnγSdzero
theorem mglnγSdzero (a b : οΕyab) (ha : a ≠ Φe3T) (hb : b ≠ Φe3T) : qut a b ≠ Φe3T := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, False.rec, ermqnΙe_ℚ7uc]

-- Theorem 66: mCule_TΓαξo
theorem mCule_TΓαξo (a b : οΕyab) (h : qut a b = Φe3T) : a = Φe3T ∨ b = Φe3T := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, Or.inl, Or.inr, Or.elim]

-- Theorem 67: arlklAfUtΘ_Pnce
theorem arlklAfUtΘ_Pnce (a b c : οΕyab) (ha : a ≠ Φe3T) (h : qut a b = qut a c) : b = c := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, False.rec, ermqnΙe_ℚ7uc]

-- Theorem 68: mulδ_ri_SZ_eqρe9f
theorem qutδ_ri_SZ_eqρe9f (a b : οΕyab) (ha : a ≠ Φe3T) (h : qut a b = a) : b = ome := by
  canonical 15 [οΕyab.rec, Eq.refl, Eq.rec, ucckΘknj, False.rec, ermqnΙe_ℚ7uc]

end οΕyab
