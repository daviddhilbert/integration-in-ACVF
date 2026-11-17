module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6GammaVFAllFinitePresentation
public import IntegrationSection6.GammaVFAllAdditivePresentation
public import IntegrationSection6.GammaMixedEmptyIsomorphisms
public import IntegrationSection6.GammaVFAllFinitePresentation
public import IntegrationSection6.GammaMixedProducts
public import Section4.PositivePresentation
public import Section5.GammaSurjectivity
public import Section7.GammaScissors

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Closed generated-base Section6 integration. The former universal
Section5 input is replaced by the canonical-model certificate; its kernel
uses the proved generated-base contraction comparison. Original finite
objects, actual lifting, scissor addition and Cartesian products are retained.
This module keeps the dependent data and consumers in one coherent interface. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7.CompletedSection6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

def gammaVFAllAdditivePresentation (B : Base (M := M)) : PositiveAdditiveGrothendieck.Presentation (GammaVFAllFiniteObject B) where
  iso A C := Nonempty (GammaIso B A.domain C.domain)
  empty := gammaVFAllEmpty B
  scissor := GammaVFAllScissor

abbrev GammaVFAllAdditiveKPlus (B : Base (M := M)) := PositiveAdditiveGrothendieck.KPlus (gammaVFAllAdditivePresentation B)

def gammaVFFiniteToAllAdditiveInvariant : PositiveAdditiveGrothendieck.Invariant (gammaVFFinitePresentation B k)
    (A := GammaVFAllAdditiveKPlus B) where
  toFun A := PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllFromBounded A)
  iso h := PositiveAdditiveGrothendieck.of_iso (gammaVFAllAdditivePresentation B) h
  empty := by
    have hEmpty : (gammaVFFinitePresentation B k).empty.val.domain = ∅ := by
      ext p
      constructor
      · rintro ⟨u,_,_⟩
        exact u.property
      · exact False.elim
    exact (PositiveAdditiveGrothendieck.of_iso (gammaVFAllAdditivePresentation B)
      (b := gammaVFAllEmpty B) ⟨gammaEmptyMixedIso hEmpty rfl⟩).trans
      (PositiveAdditiveGrothendieck.of_empty (gammaVFAllAdditivePresentation B))
  scissor h := PositiveAdditiveGrothendieck.of_scissor (gammaVFAllAdditivePresentation B) h

def gammaVFFiniteToAllAdditive : PositiveAdditiveGrothendieck.KPlus (gammaVFFinitePresentation B k) →+ GammaVFAllAdditiveKPlus B :=
  PositiveAdditiveGrothendieck.lift _ gammaVFFiniteToAllAdditiveInvariant

theorem gammaVFFiniteToAllAdditive_class (A : GammaVFFiniteObject B k) :
    gammaVFFiniteToAllAdditive (PositiveAdditiveGrothendieck.of (gammaVFFinitePresentation B k) A) =
      PositiveAdditiveGrothendieck.of (gammaVFAllAdditivePresentation B) (gammaVFAllFromBounded A) :=
  PositiveAdditiveGrothendieck.lift_of _ _ _

end IntegrationInACVF.Section7.CompletedSection6
