import IntegrationSection5.GammaFocusSection
import Section5.GammaLift

/-! Actual scalar replacement maps with full original-Gamma graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m u w : ℕ}
variable {A : Set (Point (M := M) n m)} {B : Set (Point (M := M) u w)}

theorem gamma_scalar_replacement_graph (i : Fin n) (g : A → VF (M := M))
    (hg : GammaScalarGraphDefinable G (fun p y => ∃ a : A, a.val = p ∧ g a = y)) :
    GammaGraphDefinable G (fun p q => ∃ a : A, a.val = p ∧ replace i a.val (g a) = q) := by
  have h := (gammaLogicInput G).scalar_image_graph hg (replacementGraphMap i G.real)
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨z,x,⟨a,ha,hx⟩,he⟩
    have hh := (replacementGraphMap_apply i G.real z x).symm.trans he
    have hp := congrArg Prod.fst hh
    have hq := congrArg Prod.snd hh
    exact ⟨a,ha.trans hp,(congrArg (fun z => replace i z (g a)) ha).trans
      ((congrArg (replace i z) hx).trans hq)⟩
  · rintro ⟨a,ha,hq⟩
    exact ⟨a.val,g a,⟨a,rfl,rfl⟩,(replacementGraphMap_apply i G.real a.val (g a)).trans (Prod.ext ha hq)⟩

def scalarUpdateTarget (i : Fin n) (g : A → VF (M := M)) : Set (Point (M := M) n m) :=
  Set.range (fun a : A => replace i a.val (g a))

def scalarUpdateIso (i : Fin n) (g : A → VF (M := M))
    (hg : GammaScalarGraphDefinable G (fun p y => ∃ a : A, a.val = p ∧ g a = y))
    (hinj : Function.Injective (fun a : A => replace i a.val (g a))) :
    GammaIso G A (scalarUpdateTarget i g) where
  equiv := Equiv.ofInjective _ hinj
  graph := gamma_scalar_replacement_graph i g hg

theorem scalarUpdateIso_unary (i : Fin n) (g : A → VF (M := M))
    (hg : GammaScalarGraphDefinable G (fun p y => ∃ a : A, a.val = p ∧ g a = y))
    (hinj : Function.Injective (fun a : A => replace i a.val (g a)))
    (a : A) (j : Fin n) (hji : j ≠ i) :
    ((scalarUpdateIso i g hg hinj).equiv a).val.1 j = a.val.1 j := by
  exact Function.update_of_ne hji _ _

theorem gamma_iso_precomp_scalar (e : GammaIso G A B) (g : B → VF (M := M))
    (hg : GammaScalarGraphDefinable G (fun p y => ∃ b : B, b.val = p ∧ g b = y)) :
    GammaScalarGraphDefinable G (fun p y => ∃ a : A, a.val = p ∧ g (e.equiv a) = y) := by
  apply GammaGraphDefinable.congr ((gammaLogicInput G).comp_graph e.graph hg)
  intro p q
  constructor
  · rintro ⟨z,⟨a,ha,haz⟩,b,hb,hgq⟩
    have hba : b = e.equiv a := Subtype.ext (hb.trans haz.symm)
    exact ⟨a,ha,hba ▸ hgq⟩
  · rintro ⟨a,ha,hgq⟩
    exact ⟨(e.equiv a).val,⟨a,ha,rfl⟩,e.equiv a,rfl,hgq⟩

end IntegrationInACVF.Section5
