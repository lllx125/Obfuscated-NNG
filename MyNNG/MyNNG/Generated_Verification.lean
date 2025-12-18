import Mathlib.Tactic.ApplyAt
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Use
import Mathlib.Tactic.Tauto

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

theorem ωΙξaινη7 (n : Η0Ja) : ΚxΝ GnΑ0 n = n := by
  induction n with
  | GnΑ0 =>
    rw [Ε6ΖΜF_Zζ]
  | Θ7Κr d ih =>
    rw [Qγx1dtΨo,ih]

theorem gXqΧΔℝvO (a b : Η0Ja) : ΚxΝ (Θ7Κr a) b = Θ7Κr (ΚxΝ a b)  := by
  induction b with
  | GnΑ0 =>
    rw [Ε6ΖΜF_Zζ,Ε6ΖΜF_Zζ]
  | Θ7Κr d ih =>
    rw [Qγx1dtΨo,ih,Qγx1dtΨo]

theorem KΩΦzαυωT (a b : Η0Ja) : ΚxΝ a b = ΚxΝ b a := by
  induction b with
  | GnΑ0 =>
    rw [Ε6ΖΜF_Zζ, ωΙξaινη7]
  | Θ7Κr d ih =>
    rw [Qγx1dtΨo, ih, gXqΧΔℝvO]

theorem nv3ΧWtℕsL (a b c : Η0Ja) : ΚxΝ (ΚxΝ a b) c = ΚxΝ a (ΚxΝ b c) := by
  induction c with
  | GnΑ0 =>
    rw [Ε6ΖΜF_Zζ, Ε6ΖΜF_Zζ]
  | Θ7Κr d ih =>
    rw [Qγx1dtΨo, Qγx1dtΨo, ih, Qγx1dtΨo]

theorem ΝκdWγΤσkbcΚFNΒ (a b c : Η0Ja) : ΚxΝ (ΚxΝ a b) c = ΚxΝ (ΚxΝ a c) b := by
  rw [nv3ΧWtℕsL]
  rw [KΩΦzαυωT b, nv3ΧWtℕsL]

theorem dℚN_γK8ο9d'pχρ (a b c : Η0Ja) : ΚxΝ a (ΚxΝ b c) = ΚxΝ b (ΚxΝ a c) := by
  rw [← nv3ΧWtℕsL]
  rw [KΩΦzαυωT a b]
  rw [nv3ΧWtℕsL]

theorem SZuΟvETq_ιWνJe (n : Η0Ja) : Θ7Κr n = ΚxΝ n gfΧ := by
  rw [U3ωΘτ_q_7oH_ℂe9no]
  rw [Qγx1dtΨo, Ε6ΖΜF_Zζ]

theorem T7WδnΕΝFtℂεymne (x y z : Η0Ja) (h1 : ΚxΝ x y = Wre0) (h2 : ΚxΝ (ΕWβ χΗΡd x) z = oVΟ) : ΚxΝ x y = Wre0 := by
  exact h1

theorem Nσ0lLiΞpWγjΜυℝ (x y : Η0Ja) (h : ΚxΝ GnΑ0 x = ΚxΝ (ΚxΝ GnΑ0 y) oVΟ) : x = ΚxΝ y oVΟ := by
  rw [ωΙξaινη7] at h
  rw [ωΙξaινη7] at h
  exact h

theorem iΙpχnχct2ΧttΘ4aΗ (x y : Η0Ja) (h1 : x = χΗΡd) (h2 : x = χΗΡd → y = Wre0) : y = Wre0 := by
  apply h2 at h1
  exact h1

theorem immΑRioΝΒ5κSc_sI (x : Η0Ja) (h : ΚxΝ x gfΧ = Wre0) : x = χΗΡd := by
  rw [U3ωΘτ_q_7oH_ℂe9no] at h
  rw [XfξHc_eqζΗJcιrVEr9] at h
  rw [Qγx1dtΨo] at h
  apply o5Εgγtdvl at h
  rw [Ε6ΖΜF_Zζ] at h
  exact h

theorem ovΓΡFΓctCκHνℂℂπi (x : Η0Ja) : x = Wre0 → x = Wre0 := by
  intro h
  exact h

theorem VθξΚΥΝtΟΑdΗjγx (x y : Η0Ja) : ΚxΝ x gfΧ = ΚxΝ y gfΧ → x = y := by
  intro h
  rw[U3ωΘτ_q_7oH_ℂe9no] at h
  rw[Qγx1dtΨo,Qγx1dtΨo] at h
  apply o5Εgγtdvl at h
  rw[Ε6ΖΜF_Zζ,Ε6ΖΜF_Zζ] at h
  exact h

theorem ωΜνpdRκΧ1tK_seΩ_ (x y : Η0Ja) (h1 : x = y) (h2 : x ≠ y) : False := by
  apply h2 at h1
  exact h1

theorem ρUμΞYe'u9Απ : (GnΑ0 : Η0Ja) ≠ gfΧ := by
  intro h
  rw [U3ωΘτ_q_7oH_ℂe9no] at h
  apply ΙΩζβτeΜwυ'ec at h
  exact h

theorem oβθΤMΚιΑyor : (gfΧ : Η0Ja) ≠ GnΑ0 := by
  symm
  exact ρUμΞYe'u9Απ

theorem vτδZμ3θ_ΩtwqKμ9fψiΘ : ΚxΝ (Θ7Κr (Θ7Κr GnΑ0)) (Θ7Κr (Θ7Κr GnΑ0)) ≠ Θ7Κr (Θ7Κr (Θ7Κr (Θ7Κr (Θ7Κr GnΑ0)))) := by
  intro h
  rw [Qγx1dtΨo, Qγx1dtΨo, Ε6ΖΜF_Zζ] at h
  repeat apply o5Εgγtdvl at h
  apply ΙΩζβτeΜwυ'ec at h
  exact h

theorem Rμl53fxρz (a b c d : Η0Ja) : ΚxΝ (ΚxΝ a b) (ΚxΝ c d) = ΚxΝ (ΚxΝ (ΚxΝ a c) d) b := by
  repeat rw [nv3ΧWtℕsL]
  rw [dℚN_γK8ο9d'pχρ b c]
  rw [KΩΦzαυωT b d]

theorem sαAιΕLζFrVp (a : Η0Ja) : Θ7Κr a ≠ GnΑ0 := by
  intro h
  rw [← OiiFkEΖ__bp a]
  rw [h]
  rw [I4ξΒℤk_z8ξΩν]
  trivial

theorem βΖLMclΥhℂuΘ (m n : Η0Ja) (h : m ≠ n) : Θ7Κr m ≠ Θ7Κr n := by
  contrapose! h
  apply o5Εgγtdvl at h
  exact h

theorem ΤyΥewev (m : Η0Ja) : ΕWβ m gfΧ = m := by
  rw [U3ωΘτ_q_7oH_ℂe9no]
  rw [ΑΩ7Ξ3νnr]
  rw [θ'vxθΑfφ]
  rw [ωΙξaινη7]

theorem ωCΥiCazτ (m : Η0Ja) : ΕWβ GnΑ0 m = GnΑ0 := by
  induction m with
  | GnΑ0 =>
    rw [θ'vxθΑfφ]
  | Θ7Κr d ih =>
    rw [ΑΩ7Ξ3νnr, ih, ωΙξaινη7]

theorem Ν_zivκyA (a b : Η0Ja) : ΕWβ (Θ7Κr a) b = ΚxΝ (ΕWβ a b) b := by
  induction b with
  | GnΑ0 =>
    rw [θ'vxθΑfφ, θ'vxθΑfφ, Ε6ΖΜF_Zζ]
  | Θ7Κr d hd =>
    rw [ΑΩ7Ξ3νnr, ΑΩ7Ξ3νnr, hd, Qγx1dtΨo, Qγx1dtΨo, ΝκdWγΤσkbcΚFNΒ]

theorem ΧFΤΟξrdψ (a b : Η0Ja) : ΕWβ a b = ΕWβ b a := by
  induction b with
  | GnΑ0 =>
    rw [ωCΥiCazτ]
    rw [θ'vxθΑfφ]
  | Θ7Κr d hd =>
    rw [Ν_zivκyA]
    rw [← hd]
    rw [ΑΩ7Ξ3νnr]

theorem ℝzΗσℝcψ (m : Η0Ja) : ΕWβ gfΧ m = m := by
  rw [ΧFΤΟξrdψ, ΤyΥewev]

theorem ΙΦΔVfe9 (m : Η0Ja) : ΕWβ oVΟ m = ΚxΝ m m := by
  rw [ℚJo_ℕΧΑkUvKΝne, Ν_zivκyA, ℝzΗσℝcψ]

theorem Ωψ'YiΑσ (a b c : Η0Ja) : ΕWβ a (ΚxΝ b c) = ΚxΝ (ΕWβ a b) (ΕWβ a c) := by
  induction c with
  | GnΑ0 =>
    rw [Ε6ΖΜF_Zζ, θ'vxθΑfφ, Ε6ΖΜF_Zζ]
  | Θ7Κr d hd =>
    rw [Qγx1dtΨo, ΑΩ7Ξ3νnr, hd, ΑΩ7Ξ3νnr, nv3ΧWtℕsL]

theorem eexzzm_ (a b c : Η0Ja) : ΕWβ (ΚxΝ a b) c = ΚxΝ (ΕWβ a c) (ΕWβ b c) := by
  rw [ΧFΤΟξrdψ, Ωψ'YiΑσ]
  repeat rw [ΧFΤΟξrdψ c]

theorem ℚQswΘΟVνy (a b c : Η0Ja) : ΕWβ (ΕWβ a b) c = ΕWβ a (ΕWβ b c)  := by
  induction c with
  | GnΑ0 =>
    rw [θ'vxθΑfφ, θ'vxθΑfφ, θ'vxθΑfφ]
  | Θ7Κr d ih =>
    rw [ΑΩ7Ξ3νnr, ΑΩ7Ξ3νnr, ih, Ωψ'YiΑσ]

theorem dσvrJφMβqℝYr0 : νΦΗ (GnΑ0 : Η0Ja)  GnΑ0 = gfΧ := by
  rw [φΜwoΓvΞΦ]

theorem wzKξΔΕevEΕcrz (m : Η0Ja) : νΦΗ (GnΑ0 : Η0Ja) (Θ7Κr m) = GnΑ0 := by
  rw [t4πℂ'Rτ]
  rw [θ'vxθΑfφ]

theorem hℚyaτxΦ (a : Η0Ja) : νΦΗ a gfΧ = a  := by
  rw [U3ωΘτ_q_7oH_ℂe9no]
  rw [t4πℂ'Rτ]
  rw [φΜwoΓvΞΦ]
  rw [ℝzΗσℝcψ]

theorem sYJδΓνΩ (m : Η0Ja) : νΦΗ (gfΧ : Η0Ja) m = gfΧ := by
  induction m with
  | GnΑ0 =>
    rw [φΜwoΓvΞΦ]
  | Θ7Κr t ht =>
    rw [t4πℂ'Rτ]
    rw [ht]
    rw [ℝzΗσℝcψ]

theorem ΓpKΚYδω (a : Η0Ja) : νΦΗ a oVΟ = ΕWβ a a := by
  rw [ℚJo_ℕΧΑkUvKΝne]
  rw [t4πℂ'Rτ]
  rw [hℚyaτxΦ]

theorem ΗAΥuZΡd (a m n : Η0Ja) : νΦΗ a (ΚxΝ m n) = ΕWβ (νΦΗ a m) (νΦΗ a n) := by
  induction n with
  | GnΑ0 =>
    rw [Ε6ΖΜF_Zζ]
    rw [φΜwoΓvΞΦ]
    rw [ΤyΥewev]
  | Θ7Κr t ht =>
    rw [Qγx1dtΨo]
    rw [t4πℂ'Rτ]
    rw [t4πℂ'Rτ]
    rw [ht]
    rw [ℚQswΘΟVνy]

theorem HζιξQoκ (a b n : Η0Ja) : νΦΗ (ΕWβ a b) n = ΕWβ (νΦΗ a n) (νΦΗ b n) := by
  induction n with
  | GnΑ0 =>
    repeat rw [φΜwoΓvΞΦ]
    rw [ℝzΗσℝcψ]
  | Θ7Κr t ht =>
    repeat rw [t4πℂ'Rτ]
    rw [ht]
    rw [ℚQswΘΟVνy]
    rw [ΧFΤΟξrdψ (νΦΗ b t) (ΕWβ a b)]
    rw [ΧFΤΟξrdψ (νΦΗ b t) b]
    repeat rw [← ℚQswΘΟVνy]

theorem Xωο'Aεk (a m n : Η0Ja) : νΦΗ (νΦΗ a m) n = νΦΗ a (ΕWβ m n) := by
  induction n with
  | GnΑ0 =>
    rw [θ'vxθΑfφ]
    rw [φΜwoΓvΞΦ]
    rw [φΜwoΓvΞΦ]
  | Θ7Κr t ht =>
    rw [t4πℂ'Rτ]
    rw [ht]
    rw [ΑΩ7Ξ3νnr]
    rw [ΗAΥuZΡd]

theorem ΚΚlwMW (a b : Η0Ja) : νΦΗ (ΚxΝ a b) oVΟ = ΚxΝ (ΚxΝ (νΦΗ a oVΟ) (νΦΗ b oVΟ)) (ΕWβ (ΕWβ oVΟ a) b) := by
  rw [ΓpKΚYδω, ΓpKΚYδω, ΓpKΚYδω]
  rw [ΝκdWγΤσkbcΚFNΒ]
  rw [Ωψ'YiΑσ, eexzzm_, eexzzm_]
  rw [ΙΦΔVfe9, eexzzm_]
  rw [ΧFΤΟξrdψ b a]
  rw [← nv3ΧWtℕsL, ← nv3ΧWtℕsL]

theorem γdκDχkΩΨρη_eaΔcU (a b n : Η0Ja) : ΚxΝ a n = ΚxΝ b n → a = b := by
  induction n with
  | GnΑ0 =>
    intro h
    rw [Ε6ΖΜF_Zζ, Ε6ΖΜF_Zζ] at h
    exact h
  | Θ7Κr d ih =>
    intro h
    rw [Qγx1dtΨo, Qγx1dtΨo] at h
    apply o5Εgγtdvl at h
    apply ih
    exact h

theorem TeL1SWχπRβcζνl (a b n : Η0Ja) : ΚxΝ n a = ΚxΝ n b → a = b := by
  repeat rw [KΩΦzαυωT n]
  intro h
  apply γdκDχkΩΨρη_eaΔcU at h
  exact h

theorem _adiΜ2ieMΩeaΖΒΞK (x y : Η0Ja) : ΚxΝ x y = y → x = GnΑ0 := by
  intro h
  nth_rewrite 2 [← ωΙξaινη7 y] at h
  apply γdκDχkΩΨρη_eaΔcU at h
  exact h

theorem ΔKσ_ivζgΜtοδsIdd (x y : Η0Ja) : ΚxΝ x y = x → y = GnΑ0 := by
  intro h
  nth_rewrite 2 [← ωΙξaινη7 x] at h
  nth_rewrite 2 [KΩΦzαυωT] at h
  apply TeL1SWχπRβcζνl at h
  exact h

theorem ρdd'xZgνhtοSssΨEW (a b : Η0Ja) : ΚxΝ a b = GnΑ0 → a = GnΑ0 := by
  induction b with
  | GnΑ0 =>
    intro h
    rw [Ε6ΖΜF_Zζ] at h
    exact h
  | Θ7Κr d ih =>
    intro h
    rw [Qγx1dtΨo] at h
    symm at h
    apply ΙΩζβτeΜwυ'ec at h
    cases h

theorem ηΡdnPHf9_ℂE_zXGΚ (a b : Η0Ja) : ΚxΝ a b = GnΑ0 → b = GnΑ0 := by
  rw [KΩΦzαυωT]
  exact ρdd'xZgνhtοSssΨEW b a

theorem W0ΚSδπ8ψ (x : Η0Ja) : IJ x x := by
  use GnΑ0
  rw [Ε6ΖΜF_Zζ]

theorem aτPWZ1β (x : Η0Ja) : IJ GnΑ0 x := by
  use x
  rw [ωΙξaινη7]

theorem H'5sqeo8gsPΜχ (x : Η0Ja) : IJ x (Θ7Κr x) := by
  use gfΧ
  rw [U3ωΘτ_q_7oH_ℂe9no]
  rw [Qγx1dtΨo]
  rw [Ε6ΖΜF_Zζ]

theorem Z'Ie'ΗΥνΟC (x y z : Η0Ja) (hxy : IJ x y) (hyz : IJ y z) : IJ x z := by
  cases hxy with
  | intro a ha =>
    cases hyz with
    | intro b hb =>
      apply Exists.intro (ΚxΝ a b)
      rw [hb, ha]
      rw [nv3ΧWtℕsL]

theorem qΜ3γv_p (x : Η0Ja) (hx : IJ x GnΑ0) : x = GnΑ0 := by
  cases hx with
  | intro a ha =>
    symm at ha
    apply ρdd'xZgνhtοSssΨEW at ha
    exact ha

theorem F3ΥπΔωψPuXEι (x y : Η0Ja) (hxy : IJ x y) (hyx : IJ y x) : x = y := by
  cases hxy with
  | intro a ha =>
    cases hyx with
    | intro b hb =>
      rw [ha]
      rw [ha, nv3ΧWtℕsL] at hb
      symm at hb
      apply ΔKσ_ivζgΜtοδsIdd at hb
      apply ρdd'xZgνhtοSssΨEW at hb
      rw [hb, Ε6ΖΜF_Zζ]

theorem ΙIℂpEmρ (x y : Η0Ja) (h : x = Wre0 ∨ y = χΗΡd) : y = χΗΡd ∨ x = Wre0 := by
  cases h with
  | inl hx =>
    right
    rw [hx]
  | inr hy =>
    left
    rw [hy]

theorem ℂΒe1TΘνΑ (x y : Η0Ja) : (IJ x y) ∨ (IJ y x) := by
  induction y with
  | GnΑ0 =>
    right
    exact aτPWZ1β x
  | Θ7Κr d hd =>
    cases hd with
    | inl h1 =>
      left
      cases h1 with
      | intro e h1 =>
        rw [h1]
        use ΚxΝ e gfΧ
        rw [SZuΟvETq_ιWνJe, nv3ΧWtℕsL]
    | inr h2 =>
      cases h2 with
      | intro e he =>
        cases e with
        | GnΑ0 =>
          rw [he]
          left
          rw [Ε6ΖΜF_Zζ]
          use gfΧ
          exact SZuΟvETq_ιWνJe d
        | Θ7Κr a =>
          right
          use a
          rw [Qγx1dtΨo] at he
          rw [gXqΧΔℝvO]
          exact he

theorem llγℝΕeΤuαπZ (x y : Η0Ja) (hx : IJ (Θ7Κr x) (Θ7Κr y)) : IJ x y := by
  cases hx with
  | intro d hd =>
    use d
    rw [gXqΧΔℝvO] at hd
    apply o5Εgγtdvl at hd
    exact hd

theorem xCUυ_κ (x : Η0Ja) (hx : IJ x gfΧ) : x = GnΑ0 ∨ x = gfΧ := by
  induction x with
  | GnΑ0 =>
    left
    rfl
  | Θ7Κr d hd =>
    right
    rw[U3ωΘτ_q_7oH_ℂe9no] at hx
    apply llγℝΕeΤuαπZ at hx
    apply qΜ3γv_p at hx
    rw [hx]
    rfl

theorem ℂofwoΔ (x : Η0Ja) (hx : IJ x oVΟ) : x = GnΑ0 ∨ x = gfΧ ∨ x = oVΟ := by
  cases x with
  | GnΑ0 =>
    left
    rfl
  | Θ7Κr y =>
    cases y with
    | GnΑ0 =>
      right
      left
      rw [U3ωΘτ_q_7oH_ℂe9no]
    | Θ7Κr z =>
      rw [ℚJo_ℕΧΑkUvKΝne, U3ωΘτ_q_7oH_ℂe9no] at hx ⊢
      apply llγℝΕeΤuαπZ at hx
      apply llγℝΕeΤuαπZ at hx
      apply qΜ3γv_p at hx
      rw [hx]
      right
      right
      rfl

theorem RΤwAαd_lΡψα9MI (x : Η0Ja) : IJ x (ΚxΝ gfΧ x) := by
  use gfΧ
  rw [KΩΦzαυωT]

theorem OΩηaζδ4φh (x : Η0Ja) : IJ x  x := by
  use GnΑ0
  rw [Ε6ΖΜF_Zζ]

theorem CnΚδuΓc (a b : Η0Ja) : IJ a b → IJ a (Θ7Κr b) := by
  intro h
  cases h with
  | intro c hc =>
    use Θ7Κr c
    rw [hc]
    rw [Qγx1dtΨo]

theorem ΤκSυEcveAul_ιΧΗt (a b t : Η0Ja) (h : IJ a b) : IJ (ΕWβ a t) (ΕWβ b t) := by
  cases h with
  |intro d hd =>
    use ΕWβ d t
    rw [hd, eexzzm_]

theorem hβTzHℚlpta22αzro (a b : Η0Ja) (h : ΕWβ a b ≠ GnΑ0) : b ≠ GnΑ0 := by
  intro hb
  apply h
  rw [hb, θ'vxθΑfφ]

theorem edΦΝuseUf_nρΥcυzχθ (a : Η0Ja) (ha : a ≠ GnΑ0) : ∃ n, a = Θ7Κr n := by
  induction a with
  | GnΑ0 => contradiction
  | Θ7Κr d =>
    use d

theorem n_ℕe_ilμΔn1οNwΘS (a : Η0Ja) (ha : a ≠ GnΑ0) : IJ gfΧ a := by
  apply edΦΝuseUf_nρΥcυzχθ at ha
  cases ha with
  |intro n hn =>
    use n
    rw [hn, SZuΟvETq_ιWνJe, KΩΦzαυωT]

theorem J'NjFO2DnθREt (a b : Η0Ja) (h : ΕWβ a b ≠ GnΑ0) : IJ a (ΕWβ a b) := by
  apply hβTzHℚlpta22αzro at h
  apply n_ℕe_ilμΔn1οNwΘS at h
  apply ΤκSυEcveAul_ιΧΗt gfΧ b a at h
  rw [ℝzΗσℝcψ, ΧFΤΟξrdψ] at h
  exact h

theorem rXΝlriLRt_qjhΩυe (x y : Η0Ja) (h : ΕWβ x y = gfΧ) : x = gfΧ := by
  have h2 : ΕWβ x y ≠ GnΑ0 := by
    rw [h, U3ωΘτ_q_7oH_ℂe9no]
    symm
    apply ΙΩζβτeΜwυ'ec
  apply J'NjFO2DnθREt at h2
  rw [h] at h2
  apply xCUυ_κ at h2
  cases h2 with
  |inl h0 =>
    rw [h0] at h
    rw [ωCΥiCazτ] at h
    cases h
  |inr h1 =>
    exact h1

theorem eΦ6τΔΥZξℕmΥ (a b : Η0Ja) (ha : a ≠ GnΑ0) (hb : b ≠ GnΑ0) : ΕWβ a b ≠ GnΑ0 := by
  apply edΦΝuseUf_nρΥcυzχθ at ha
  apply edΦΝuseUf_nρΥcυzχθ at hb
  cases ha with
  |intro c hc =>
    cases hb with
    |intro d hd =>
      rw [hc, hd]
      rw [ΑΩ7Ξ3νnr, Qγx1dtΨo]
      symm
      apply ΙΩζβτeΜwυ'ec

theorem ℝRΞΧJRℂYψeℕ (a b : Η0Ja) (h : ΕWβ a b = GnΑ0) : a = GnΑ0 ∨ b = GnΑ0 := by
  have h2 := eΦ6τΔΥZξℕmΥ a b
  tauto

theorem ℝuΒwplυtcΔσTΑξ (a b c : Η0Ja) (ha : a ≠ GnΑ0) (h : ΕWβ a b = ΕWβ a c) : b = c := by
  revert c
  induction b with
  | GnΑ0 =>
    intro c h
    rw [θ'vxθΑfφ] at h
    symm at h
    apply ℝRΞΧJRℂYψeℕ at h
    cases h with
    |inl ha0 => contradiction
    |inr hc0 =>
      rw [hc0]
  | Θ7Κr d ih =>
    intro c h
    induction c with
    | GnΑ0 =>
      rw [θ'vxθΑfφ] at h
      apply ℝRΞΧJRℂYψeℕ at h
      cases h with
      |inl ha0 => contradiction
      |inr hc0 => contradiction
    | Θ7Κr e he =>
      rw [ΑΩ7Ξ3νnr, ΑΩ7Ξ3νnr] at h
      apply γdκDχkΩΨρη_eaΔcU at h
      apply ih at h
      rw [h]

theorem fρMlxDhCwΒβpYsΙf (a b : Η0Ja) (ha : a ≠ GnΑ0) (h : ΕWβ a b = a) : b = gfΧ := by
  nth_rewrite 2 [← ΤyΥewev a] at h
  exact ℝuΒwplυtcΔσTΑξ a b gfΧ ha h

end Η0Ja
