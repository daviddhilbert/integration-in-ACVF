import IntegrationSection6.FiniteGammaObjects

/-! Elementary blowups at a fixed real code presentation, with the
original Gamma graphs and finite-volume lift isomorphism retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def gammaElementaryAt {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (U : GammaObjectAt B S n) (i : Fin n)
    (h : GammaAdmissible U.toGamma.toGammaRVObject i) : GammaObjectAt B S n where
  object := ofGamma (gammaFiniteElementaryBasic hκ hs h00 hsmall  U.toGamma i h)
  real_contains := U.real_contains
  domain_graph := (gammaFiniteElementaryBasic hκ hs h00 hsmall  U.toGamma i h).domain_graph
  volume_graph := (gammaFiniteElementaryBasic hκ hs h00 hsmall  U.toGamma i h).volume_graph

@[simp] theorem gammaElementaryAt_object {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (U : GammaObjectAt B S n) (i : Fin n)
    (h : GammaAdmissible U.toGamma.toGammaRVObject i) :
    (gammaElementaryAt hκ hs h00 hsmall  U i h).object.obj = @IntegrationInACVF.Section6.elementary M N hN S n U.object.obj i := rfl

theorem gammaElementaryAt_liftIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (hB : VFGammaGeneratedBase B) (U : GammaObjectAt B S n) (i : Fin n)
    (h : GammaAdmissible U.toGamma.toGammaRVObject i) :
    Nonempty (GammaIso B U.toGamma.lift (gammaElementaryAt hκ hs h00 hsmall  U i h).toGamma.lift) :=
  elementary_lifts_isomorphic hκ hs h00 hsmall hB h

end IntegrationInACVF.Section6.FiniteRV
