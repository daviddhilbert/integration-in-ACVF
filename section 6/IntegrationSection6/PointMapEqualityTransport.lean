import IntegrationSection5.RelativeSpecial
import IntegrationSection5.GammaGraphOperations

/-! Equality transport of the target of an actual point map retains its
values, relative specialness and complete original-Gamma graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {B : Base (M := M)} {n a b : ℕ}
variable {U : DefSet (M := M) S n a} {V V' : DefSet (M := M) S n b}

def pointMapCastTarget (f : Map U V) (h : V = V') : Map U V' := h ▸ f

theorem pointMapCastTarget_value (f : Map U V) (h : V = V') (u : U) :
    ((pointMapCastTarget f h) u).val = (f u).val := by cases h; rfl

theorem specialRelative_pointMapCastTarget (f : Map U V) (h : V = V') {i : Fin n}
    (hf : SpecialRelative f i) : SpecialRelative (pointMapCastTarget f h) i := by cases h; exact hf

theorem gamma_pointMapCastTarget (f : Map U V) (h : V = V')
    (hf : GammaGraphDefinable B (pointMapGraph f)) : GammaGraphDefinable B (pointMapGraph (pointMapCastTarget f h)) := by
  cases h
  exact hf

theorem pointMapCastTarget_bijective (f : Map U V) (h : V = V') (hf : Function.Bijective f) :
    Function.Bijective (pointMapCastTarget f h) := by cases h; exact hf

end IntegrationInACVF.Section6
