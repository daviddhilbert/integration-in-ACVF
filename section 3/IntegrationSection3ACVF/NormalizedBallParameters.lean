import IntegrationSection3ACVF.MaximalOpenClasses

/-! Normalization preserves entire same-radius ball families. Gamma
quotients are kept distinct; the bridge uses a common nonzero RV code
and equality of the actual ball point sets for every centre. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.NamedRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.NormalizedBallParameters

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "N" => @CanonicalStructure.normalize M sM
local notation "hN" => @CanonicalStructure.normalized_model M sM hM

theorem radius_normalize (a : VFType (M := M)) (t : M) (ht : iRV t) (strict : Bool) :
    @radiusBall M N ⟨a.val,a.property⟩ t strict = radiusBall a t strict := by
  cases strict
  · simpa only [radiusBall,Bool.false_eq_true,false_implies,and_true] using
      closedBall_set_normalize a.val t a.property ht
  · simpa only [radiusBall,true_implies] using openBall_set_normalize a.val t a.property ht

theorem gamma_family (α : Values.Gamma (M := M)) :
    ∃ β : @Values.Gamma M N hN, ∀ a : VFType (M := M), ∀ strict : Bool,
      @gammaBall M N hN ⟨a.val,a.property⟩ β strict = gammaBall a α strict := by
  obtain ⟨t,ht0,htα⟩ := Values.gamma_has_nonzero_representative α
  have hz : @iRVZero M N = @iRVZero M sM := CanonicalStructure.sortZero_normalize .rv
  let tN : @CanonicalRV.RVSort M N := ⟨t.val,t.property⟩
  have htN : tN.val ≠ @iRVZero M N := by simpa only [hz] using ht0
  let β : @Values.Gamma M N hN := @Values.gammaOf M N hN tN htN
  refine ⟨β,?_⟩
  intro a strict
  calc
    @gammaBall M N hN ⟨a.val,a.property⟩ β strict = @radiusBall M N ⟨a.val,a.property⟩ t.val strict :=
      (@radiusBall_eq_gammaBall M N hN ⟨a.val,a.property⟩ tN β rfl strict).symm
    _ = radiusBall a t.val strict := radius_normalize a t.val t.property strict
    _ = gammaBall a α strict := radiusBall_eq_gammaBall a t α htα strict

theorem gamma_family_back (β : @Values.Gamma M N hN) :
    ∃ α : Values.Gamma (M := M), ∀ a : VFType (M := M), ∀ strict : Bool,
      @gammaBall M N hN ⟨a.val,a.property⟩ β strict = gammaBall a α strict := by
  obtain ⟨tN,htN,htβ⟩ := @Values.gamma_has_nonzero_representative M N hN β
  have hz : @iRVZero M N = @iRVZero M sM := CanonicalStructure.sortZero_normalize .rv
  let t : CanonicalRV.RVSort M := ⟨tN.val,tN.property⟩
  have ht : t.val ≠ @iRVZero M sM := by simpa only [hz] using htN
  let α : Values.Gamma (M := M) := Values.gammaOf t ht
  refine ⟨α,?_⟩
  intro a strict
  calc
    @gammaBall M N hN ⟨a.val,a.property⟩ β strict = @radiusBall M N ⟨a.val,a.property⟩ t.val strict :=
      (@radiusBall_eq_gammaBall M N hN ⟨a.val,a.property⟩ tN β htβ strict).symm
    _ = radiusBall a t.val strict := radius_normalize a t.val t.property strict
    _ = gammaBall a α strict := radiusBall_eq_gammaBall a t α rfl strict

end IntegrationInACVF.Section3ACVF.NormalizedBallParameters
