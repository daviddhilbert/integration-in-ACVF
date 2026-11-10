import IntegrationSection3ACVF.GammaRadiusAtomicity
import IntegrationSection3ACVF.PuncturedGeometry

/-!
# The sequel's ball and primitive-type predicates

Unlike the predecessor's broader open-disc convention, a singleton is not
an open ball here. VF is explicitly clopen. Radius and valuative-centre
predicates use the unchanged actual Gamma quotient, including its absorbing
infinity value and a separate bottom radius for VF.

The predicates below do not assert the primitive decomposition theorem or
original-base definability of its components.
-/

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.PuncturedGeometry

namespace IntegrationInACVF.Section3ACVF.PaperBalls

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Definition 2.2 with the sequel's explicit whole-field convention. -/
def IsOpenBall (B : Set M) : Prop :=
  B = {x | iVF x} ∨ ∃ a : VFType (M := M), ∃ γ : Values.Gamma (M := M), B = gammaBall a γ true

def IsClosedBall (B : Set M) : Prop :=
  B = {x | iVF x} ∨ (∃ a : VFType (M := M), B = {a.val}) ∨
    ∃ a : VFType (M := M), ∃ γ : Values.Gamma (M := M), B = gammaBall a γ false

abbrev Radius := WithBot (Values.GammaTop (M := M))

/-- Radius is a property of the actual parent point set, with no selected
centre or representative included in the data. -/
def HasRadius (B : Set M) (r : Radius (M := M)) : Prop :=
  (B = {x | iVF x} ∧ r = ⊥) ∨
    (∃ a : VFType (M := M), B = {a.val} ∧ r = (↑(Values.infinity (M := M)) : Radius (M := M))) ∨
    ∃ a : VFType (M := M), ∃ γ : Values.Gamma (M := M), ∃ strict : Bool,
      B = gammaBall a γ strict ∧ r = (↑γ.val : Radius (M := M))

/-- Definition 2.2's valuative centre, applied to the unpunctured parent. -/
def HasValuativeCentre (B : Set M) (c : Values.GammaTop (M := M)) : Prop :=
  if iVFZero ∈ B then c = Values.infinity else
    ∀ x : VFType (M := M), x.val ∈ B → Values.vfValueHom x = c

/-- A closed ordinary ball with precisely one maximal open subball removed.
The containing-ball and hole conditions are already part of PuncturedBall. -/
def IsThinAnnulus (d : PuncturedBall M) : Prop :=
  ∃ a b : VFType (M := M), ∃ γ : Values.Gamma (M := M),
    d.parent = gammaBall a γ false ∧ d.holes = {gammaBall b γ true}

inductive PrimitiveKind where
  | openBall | closedBall | thinAnnulus
  deriving DecidableEq

def HasPrimitiveKind (d : PuncturedBall M) : PrimitiveKind → Prop
  | .openBall => d.holes = ∅ ∧ IsOpenBall d.parent
  | .closedBall => d.holes = ∅ ∧ IsClosedBall d.parent
  | .thinAnnulus => IsThinAnnulus d

/-- Definition 3.5. Invariants refer to the parent before its holes are
removed; the primitive kind distinguishes an unpunctured ball and an annulus. -/
def SamePrimitiveType (d e : PuncturedBall M) : Prop :=
  ∃ r : Radius (M := M), ∃ c : Values.GammaTop (M := M), ∃ k : PrimitiveKind,
    (HasRadius d.parent r ∧ HasValuativeCentre d.parent c ∧ HasPrimitiveKind d k) ∧
      HasRadius e.parent r ∧ HasValuativeCentre e.parent c ∧ HasPrimitiveKind e k

theorem samePrimitiveType_symm {d e : PuncturedBall M} (h : SamePrimitiveType d e) :
    SamePrimitiveType e d := by
  obtain ⟨r,c,k,hd,he⟩ := h
  exact ⟨r,c,k,he,hd⟩

end IntegrationInACVF.Section3ACVF.PaperBalls
