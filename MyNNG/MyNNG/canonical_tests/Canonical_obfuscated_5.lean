import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Tauto
import Canonical

inductive Η0Ja where
| GnΑ0 : Η0Ja
| Θ7Κr : Η0Ja → Η0Ja

namespace Η0Ja

instance : Inhabited Η0Ja where
  default := Η0Ja.GnΑ0

opaque ΚxΝ : Η0Ja → Η0Ja → Η0Ja

axiom Ε6ΖΜF_Zζ (a : Η0Ja) : ΚxΝ a GnΑ0 = a

axiom Qγx1dtΨo (a d : Η0Ja) : ΚxΝ a (Θ7Κr d) = Θ7Κr (ΚxΝ a d)

def gkDΞ : Η0Ja → Η0Ja
| GnΑ0 => GnΑ0
| Θ7Κr n => n

theorem O0ℝΒΝDΨℕ2 (n : Η0Ja) : gkDΞ (Θ7Κr n) = n := rfl

theorem o5Εgγtdvl (a b : Η0Ja) (h : Θ7Κr a = Θ7Κr b) : a = b := by
  rw [← O0ℝΒΝDΨℕ2 a, h, O0ℝΒΝDΨℕ2]

def ℂy'tΒγ : Η0Ja → Prop
| GnΑ0 => True
| Θ7Κr _ => False

theorem I4ξΒℤk_z8ξΩν : ℂy'tΒγ GnΑ0 = True := rfl

theorem OiiFkEΖ__bp (n : Η0Ja) : ℂy'tΒγ (Θ7Κr n) = False := rfl

theorem ΙΩζβτeΜwυ'ec (a : Η0Ja) : GnΑ0 ≠ Θ7Κr a := by
  intro h
  rw [← OiiFkEΖ__bp a]
  rw [← h]
  rw [I4ξΒℤk_z8ξΩν]
  trivial
-- multiplication

opaque ΕWβ : Η0Ja → Η0Ja → Η0Ja

axiom θ'vxθΑfφ (a : Η0Ja) : ΕWβ a GnΑ0 = GnΑ0

axiom ΑΩ7Ξ3νnr (a b : Η0Ja) : ΕWβ a (Θ7Κr b) = ΚxΝ (ΕWβ a b) a

def gfΧ : Η0Ja := Η0Ja.Θ7Κr GnΑ0

def oVΟ : Η0Ja := Η0Ja.Θ7Κr gfΧ

def χΗΡd : Η0Ja := Η0Ja.Θ7Κr oVΟ

def Wre0 : Η0Ja := Η0Ja.Θ7Κr χΗΡd

theorem U3ωΘτ_q_7oH_ℂe9no : gfΧ = Θ7Κr GnΑ0 := by rfl

theorem ℚJo_ℕΧΑkUvKΝne : oVΟ = Θ7Κr gfΧ := by rfl

theorem hNX_eqΓoXβα6BΗOw : χΗΡd = Θ7Κr oVΟ := by rfl

theorem XfξHc_eqζΗJcιrVEr9 : Wre0 = Θ7Κr χΗΡd := by rfl
-- power

opaque νΦΗ : Η0Ja → Η0Ja → Η0Ja

axiom φΜwoΓvΞΦ (m : Η0Ja) : νΦΗ m GnΑ0 = gfΧ

axiom t4πℂ'Rτ (m n : Η0Ja) : νΦΗ m (Θ7Κr n) = ΕWβ (νΦΗ m n) m

def IJ (a b : Η0Ja) :=  ∃ (c : Η0Ja), b = ΚxΝ a c

theorem _iΝf'_εfApyη9tGD (a b : Η0Ja) : IJ a b ↔ ∃ (c : Η0Ja), b = ΚxΝ a c := Iff.rfl

def sXΝηkΞNΨ (a b : Η0Ja) :=  (IJ a b) ∧ ¬ (IJ b  a)

open Η0Ja

-- Theorem 1: ωΙξaινη7
theorem ωΙξaινη7 (n : Η0Ja) : ΚxΝ GnΑ0 n = n := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 2: gXqΧΔℝvO
theorem gXqΧΔℝvO (a b : Η0Ja) : ΚxΝ (Θ7Κr a) b = Θ7Κr (ΚxΝ a b)  := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 3: KΩΦzαυωT
theorem KΩΦzαυωT (a b : Η0Ja) : ΚxΝ a b = ΚxΝ b a := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 4: nv3ΧWtℕsL
theorem nv3ΧWtℕsL (a b c : Η0Ja) : ΚxΝ (ΚxΝ a b) c = ΚxΝ a (ΚxΝ b c) := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 5: ΝκdWγΤσkbcΚFNΒ
theorem ΝκdWγΤσkbcΚFNΒ (a b c : Η0Ja) : ΚxΝ (ΚxΝ a b) c = ΚxΝ (ΚxΝ a c) b := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 6: dℚN_γK8ο9d'pχρ
theorem dℚN_γK8ο9d'pχρ (a b c : Η0Ja) : ΚxΝ a (ΚxΝ b c) = ΚxΝ b (ΚxΝ a c) := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 7: SZuΟvETq_ιWνJe
theorem SZuΟvETq_ιWνJe (n : Η0Ja) : Θ7Κr n = ΚxΝ n gfΧ := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 8: T7WδnΕΝFtℂεymne
theorem T7WδnΕΝFtℂεymne (x y z : Η0Ja) (h1 : ΚxΝ x y = Wre0) (h2 : ΚxΝ (ΕWβ χΗΡd x) z = oVΟ) : ΚxΝ x y = Wre0 := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 9: Nσ0lLiΞpWγjΜυℝ
theorem Nσ0lLiΞpWγjΜυℝ (x y : Η0Ja) (h : ΚxΝ GnΑ0 x = ΚxΝ (ΚxΝ GnΑ0 y) oVΟ) : x = ΚxΝ y oVΟ := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 10: iΙpχnχct2ΧttΘ4aΗ
theorem iΙpχnχct2ΧttΘ4aΗ (x y : Η0Ja) (h1 : x = χΗΡd) (h2 : x = χΗΡd → y = Wre0) : y = Wre0 := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 11: immΑRioΝΒ5κSc_sI
theorem immΑRioΝΒ5κSc_sI (x : Η0Ja) (h : ΚxΝ x gfΧ = Wre0) : x = χΗΡd := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 12: ovΓΡFΓctCκHνℂℂπi
theorem ovΓΡFΓctCκHνℂℂπi (x : Η0Ja) : x = Wre0 → x = Wre0 := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 13: VθξΚΥΝtΟΑdΗjγx
theorem VθξΚΥΝtΟΑdΗjγx (x y : Η0Ja) : ΚxΝ x gfΧ = ΚxΝ y gfΧ → x = y := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 14: ωΜνpdRκΧ1tK_seΩ_
theorem ωΜνpdRκΧ1tK_seΩ_ (x y : Η0Ja) (h1 : x = y) (h2 : x ≠ y) : False := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl, False.rec, ΙΩζβτeΜwυ'ec]

-- Theorem 15: ρUμΞYe'u9Απ
theorem ρUμΞYe'u9Απ : (GnΑ0 : Η0Ja) ≠ gfΧ := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl, False.rec, ΙΩζβτeΜwυ'ec]

-- Theorem 16: oβθΤMΚιΑyor
theorem oβθΤMΚιΑyor : (gfΧ : Η0Ja) ≠ GnΑ0 := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl, False.rec, ΙΩζβτeΜwυ'ec]

-- Theorem 17: vτδZμ3θ_ΩtwqKμ9fψiΘ
theorem vτδZμ3θ_ΩtwqKμ9fψiΘ : ΚxΝ (Θ7Κr (Θ7Κr GnΑ0)) (Θ7Κr (Θ7Κr GnΑ0)) ≠ Θ7Κr (Θ7Κr (Θ7Κr (Θ7Κr (Θ7Κr GnΑ0)))) := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl, False.rec, ΙΩζβτeΜwυ'ec]

-- Theorem 18: Rμl53fxρz
theorem Rμl53fxρz (a b c d : Η0Ja) : ΚxΝ (ΚxΝ a b) (ΚxΝ c d) = ΚxΝ (ΚxΝ (ΚxΝ a c) d) b := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 19: sαAιΕLζFrVp
theorem sαAιΕLζFrVp (a : Η0Ja) : Θ7Κr a ≠ GnΑ0 := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl, False.rec, ΙΩζβτeΜwυ'ec]

-- Theorem 20: βΖLMclΥhℂuΘ
theorem βΖLMclΥhℂuΘ (m n : Η0Ja) (h : m ≠ n) : Θ7Κr m ≠ Θ7Κr n := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl, False.rec, ΙΩζβτeΜwυ'ec]

-- Theorem 21: ΤyΥewev
theorem ΤyΥewev (m : Η0Ja) : ΕWβ m gfΧ = m := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 22: ωCΥiCazτ
theorem ωCΥiCazτ (m : Η0Ja) : ΕWβ GnΑ0 m = GnΑ0 := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 23: Ν_zivκyA
theorem Ν_zivκyA (a b : Η0Ja) : ΕWβ (Θ7Κr a) b = ΚxΝ (ΕWβ a b) b := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 24: ΧFΤΟξrdψ
theorem ΧFΤΟξrdψ (a b : Η0Ja) : ΕWβ a b = ΕWβ b a := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 25: ℝzΗσℝcψ
theorem ℝzΗσℝcψ (m : Η0Ja) : ΕWβ gfΧ m = m := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 26: ΙΦΔVfe9
theorem ΙΦΔVfe9 (m : Η0Ja) : ΕWβ oVΟ m = ΚxΝ m m := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 27: Ωψ'YiΑσ
theorem Ωψ'YiΑσ (a b c : Η0Ja) : ΕWβ a (ΚxΝ b c) = ΚxΝ (ΕWβ a b) (ΕWβ a c) := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 28: eexzzm_
theorem eexzzm_ (a b c : Η0Ja) : ΕWβ (ΚxΝ a b) c = ΚxΝ (ΕWβ a c) (ΕWβ b c) := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 29: ℚQswΘΟVνy
theorem ℚQswΘΟVνy (a b c : Η0Ja) : ΕWβ (ΕWβ a b) c = ΕWβ a (ΕWβ b c)  := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 30: dσvrJφMβqℝYr0
theorem dσvrJφMβqℝYr0 : νΦΗ (GnΑ0 : Η0Ja)  GnΑ0 = gfΧ := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 31: wzKξΔΕevEΕcrz
theorem wzKξΔΕevEΕcrz (m : Η0Ja) : νΦΗ (GnΑ0 : Η0Ja) (Θ7Κr m) = GnΑ0 := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 32: hℚyaτxΦ
theorem hℚyaτxΦ (a : Η0Ja) : νΦΗ a gfΧ = a  := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 33: sYJδΓνΩ
theorem sYJδΓνΩ (m : Η0Ja) : νΦΗ (gfΧ : Η0Ja) m = gfΧ := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 34: ΓpKΚYδω
theorem ΓpKΚYδω (a : Η0Ja) : νΦΗ a oVΟ = ΕWβ a a := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 35: ΗAΥuZΡd
theorem ΗAΥuZΡd (a m n : Η0Ja) : νΦΗ a (ΚxΝ m n) = ΕWβ (νΦΗ a m) (νΦΗ a n) := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 36: HζιξQoκ
theorem HζιξQoκ (a b n : Η0Ja) : νΦΗ (ΕWβ a b) n = ΕWβ (νΦΗ a n) (νΦΗ b n) := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 37: Xωο'Aεk
theorem Xωο'Aεk (a m n : Η0Ja) : νΦΗ (νΦΗ a m) n = νΦΗ a (ΕWβ m n) := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 38: ΚΚlwMW
theorem ΚΚlwMW (a b : Η0Ja) : νΦΗ (ΚxΝ a b) oVΟ = ΚxΝ (ΚxΝ (νΦΗ a oVΟ) (νΦΗ b oVΟ)) (ΕWβ (ΕWβ oVΟ a) b) := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 39: γdκDχkΩΨρη_eaΔcU
theorem γdκDχkΩΨρη_eaΔcU (a b n : Η0Ja) : ΚxΝ a n = ΚxΝ b n → a = b := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 40: TeL1SWχπRβcζνl
theorem TeL1SWχπRβcζνl (a b n : Η0Ja) : ΚxΝ n a = ΚxΝ n b → a = b := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 41: _adiΜ2ieMΩeaΖΒΞK
theorem _adiΜ2ieMΩeaΖΒΞK (x y : Η0Ja) : ΚxΝ x y = y → x = GnΑ0 := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 42: ΔKσ_ivζgΜtοδsIdd
theorem ΔKσ_ivζgΜtοδsIdd (x y : Η0Ja) : ΚxΝ x y = x → y = GnΑ0 := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 43: ρdd'xZgνhtοSssΨEW
theorem ρdd'xZgνhtοSssΨEW (a b : Η0Ja) : ΚxΝ a b = GnΑ0 → a = GnΑ0 := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 44: ηΡdnPHf9_ℂE_zXGΚ
theorem ηΡdnPHf9_ℂE_zXGΚ (a b : Η0Ja) : ΚxΝ a b = GnΑ0 → b = GnΑ0 := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 45: W0ΚSδπ8ψ
theorem W0ΚSδπ8ψ (x : Η0Ja) : IJ x x := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 46: aτPWZ1β
theorem aτPWZ1β (x : Η0Ja) : IJ GnΑ0 x := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 47: H'5sqeo8gsPΜχ
theorem H'5sqeo8gsPΜχ (x : Η0Ja) : IJ x (Θ7Κr x) := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 48: Z'Ie'ΗΥνΟC
theorem Z'Ie'ΗΥνΟC (x y z : Η0Ja) (hxy : IJ x y) (hyz : IJ y z) : IJ x z := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 49: qΜ3γv_p
theorem qΜ3γv_p (x : Η0Ja) (hx : IJ x GnΑ0) : x = GnΑ0 := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 50: F3ΥπΔωψPuXEι
theorem F3ΥπΔωψPuXEι (x y : Η0Ja) (hxy : IJ x y) (hyx : IJ y x) : x = y := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 51: ΙIℂpEmρ
theorem ΙIℂpEmρ (x y : Η0Ja) (h : x = Wre0 ∨ y = χΗΡd) : y = χΗΡd ∨ x = Wre0 := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl, Or.inl, Or.inr, Or.elim]

-- Theorem 52: ℂΒe1TΘνΑ
theorem ℂΒe1TΘνΑ (x y : Η0Ja) : (IJ x y) ∨ (IJ y x) := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl, Or.inl, Or.inr, Or.elim]

-- Theorem 53: llγℝΕeΤuαπZ
theorem llγℝΕeΤuαπZ (x y : Η0Ja) (hx : IJ (Θ7Κr x) (Θ7Κr y)) : IJ x y := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 54: xCUυ_κ
theorem xCUυ_κ (x : Η0Ja) (hx : IJ x gfΧ) : x = GnΑ0 ∨ x = gfΧ := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl, Or.inl, Or.inr, Or.elim]

-- Theorem 55: ℂofwoΔ
theorem ℂofwoΔ (x : Η0Ja) (hx : IJ x oVΟ) : x = GnΑ0 ∨ x = gfΧ ∨ x = oVΟ := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl, Or.inl, Or.inr, Or.elim]

-- Theorem 56: RΤwAαd_lΡψα9MI
theorem RΤwAαd_lΡψα9MI (x : Η0Ja) : IJ x (ΚxΝ gfΧ x) := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 57: OΩηaζδ4φh
theorem OΩηaζδ4φh (x : Η0Ja) : IJ x  x := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 58: CnΚδuΓc
theorem CnΚδuΓc (a b : Η0Ja) : IJ a b → IJ a (Θ7Κr b) := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 59: ΤκSυEcveAul_ιΧΗt
theorem ΤκSυEcveAul_ιΧΗt (a b t : Η0Ja) (h : IJ a b) : IJ (ΕWβ a t) (ΕWβ b t) := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 60: hβTzHℚlpta22αzro
theorem hβTzHℚlpta22αzro (a b : Η0Ja) (h : ΕWβ a b ≠ GnΑ0) : b ≠ GnΑ0 := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl, False.rec, ΙΩζβτeΜwυ'ec]

-- Theorem 61: edΦΝuseUf_nρΥcυzχθ
theorem edΦΝuseUf_nρΥcυzχθ (a : Η0Ja) (ha : a ≠ GnΑ0) : ∃ n, a = Θ7Κr n := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl, False.rec, ΙΩζβτeΜwυ'ec, Exists.intro, Exists.elim]

-- Theorem 62: n_ℕe_ilμΔn1οNwΘS
theorem n_ℕe_ilμΔn1οNwΘS (a : Η0Ja) (ha : a ≠ GnΑ0) : IJ gfΧ a := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl, False.rec, ΙΩζβτeΜwυ'ec]

-- Theorem 63: J'NjFO2DnθREt
theorem J'NjFO2DnθREt (a b : Η0Ja) (h : ΕWβ a b ≠ GnΑ0) : IJ a (ΕWβ a b) := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl, False.rec, ΙΩζβτeΜwυ'ec]

-- Theorem 64: rXΝlriLRt_qjhΩυe
theorem rXΝlriLRt_qjhΩυe (x y : Η0Ja) (h : ΕWβ x y = gfΧ) : x = gfΧ := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl]

-- Theorem 65: eΦ6τΔΥZξℕmΥ
theorem eΦ6τΔΥZξℕmΥ (a b : Η0Ja) (ha : a ≠ GnΑ0) (hb : b ≠ GnΑ0) : ΕWβ a b ≠ GnΑ0 := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl, False.rec, ΙΩζβτeΜwυ'ec]

-- Theorem 66: ℝRΞΧJRℂYψeℕ
theorem ℝRΞΧJRℂYψeℕ (a b : Η0Ja) (h : ΕWβ a b = GnΑ0) : a = GnΑ0 ∨ b = GnΑ0 := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl, Or.inl, Or.inr, Or.elim]

-- Theorem 67: ℝuΒwplυtcΔσTΑξ
theorem ℝuΒwplυtcΔσTΑξ (a b c : Η0Ja) (ha : a ≠ GnΑ0) (h : ΕWβ a b = ΕWβ a c) : b = c := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl, False.rec, ΙΩζβτeΜwυ'ec]

-- Theorem 68: fρMlxDhCwΒβpYsΙf
theorem fρMlxDhCwΒβpYsΙf (a b : Η0Ja) (ha : a ≠ GnΑ0) (h : ΕWβ a b = a) : b = gfΧ := by
  canonical 15 [Η0Ja.rec, Eq.refl, Eq.rec, o5Εgγtdvl, False.rec, ΙΩζβτeΜwυ'ec]

end Η0Ja
