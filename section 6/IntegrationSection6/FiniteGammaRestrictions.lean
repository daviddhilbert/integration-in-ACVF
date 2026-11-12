import IntegrationSection6.FiniteGammaChartLaws

/-! Actual finite subobjects and complements retain original-Gamma graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaRestrictAt (U : GammaObjectAt B S n)
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N
      (@rawRVSpace M N (rvObjectArity U.object.obj)) S)
    (hA : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A) ⊆ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S (rvObjectDomain U.object.obj)))
    (hΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) | p.2 ∈ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A)}) :
    GammaObjectAt B S n where
  object := ⟨@RVObject.restrict M N S n U.object.obj A hA,
    @RVObject.restrict_finite_volume M N S n U.object.obj U.object.property A hA⟩
  real_contains := U.real_contains
  domain_graph := hΓ
  volume_graph := by
    apply GammaGraphDefinable.congr ((gammaLogicInput B).restrict_graph hΓ U.volume_graph)
    intro p q
    constructor
    · rintro ⟨hp,u,hu,hq⟩
      refine ⟨⟨p.2,hp⟩,rfl,?_⟩
      have he : (⟨p.2,hA hp⟩ : rvObjectDomain U.object.obj) = u := Subtype.ext hu.symm
      change (rvObjectVolume U.object.obj ⟨p.2,hA hp⟩).val = q.2
      rw [he]
      exact hq
    · rintro ⟨u,hu,hq⟩
      refine ⟨?_,⟨u.val,hA u.property⟩,hu,hq⟩
      exact (show (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A) p.2 from hu ▸ u.property)

def gammaComplementAt (U : GammaObjectAt B S n)
    (A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N
      (@rawRVSpace M N (rvObjectArity U.object.obj)) S)
    (hΓ : GammaSetDefinable B {p : Point (M := M) 0 (rvObjectArity U.object.obj) | p.2 ∈ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ S A)}) :
    GammaObjectAt B S n :=
  gammaRestrictAt U (@complement M N S n U.object.obj A) (@complement_subset M N hN S n U.object.obj A)
    ((gammaLogicInput B).sdiff U.domain_graph hΓ)

end IntegrationInACVF.Section6.FiniteRV
