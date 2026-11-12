import IntegrationSection6.FiniteGammaIsoRealization
import IntegrationSection6.GammaGraphCoproducts

/-! A common internal code universe for finite Gamma geometry. Full
domain, volume and chart graphs remain over the original base; the
internal universe is never inserted into a saturation smallness bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

def gammaUniversalObject (U : GammaRVFiniteObject B k) : GammaObjectAt B (Set.univ : Set M) k :=
  gammaObjectAtExtend U (Set.subset_univ _)

theorem gammaUniversalIso (U V : GammaRVFiniteObject B k)
    (e : GammaRVIso U.toGammaRVObject V.toGammaRVObject) :
    Nonempty (GammaIsoAt (gammaUniversalObject U) (gammaUniversalObject V)) := by
  obtain ⟨d,t,hr⟩ := gamma_rv_relation_real_specialize e.graph
  let Q := B.real ∪ Set.range (rawTuple t)
  let A := gammaUniversalObject U
  let C := gammaUniversalObject V
  let F : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ (Set.univ : Set M)
      (rvObjectDomain A.object.obj) (rvObjectDomain C.object.obj) :=
    @SpecialTransformations.DefinableGeometry.Map.mk LRV M N _ _ _ _ _ e.equiv
      (@SpecialTransformations.DefinableGeometry.Space.RelationDefinable.mono LRV M N
      (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object))
      (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity V.object)) Q Set.univ _ hr (Set.subset_univ _))
  have hw (u : rvObjectDomain A.object.obj) :
      @rvWeight M N k (@RVObject.value M N Set.univ k A.object.obj u) =
        @rvWeight M N k (@RVObject.value M N Set.univ k C.object.obj (F u)) :=
    (rawWeight_eq_normalized_weight (gammaVolumeValue U.toGammaRVObject u)).symm.trans
      ((e.weight u).trans (rawWeight_eq_normalized_weight (gammaVolumeValue V.toGammaRVObject (e.equiv u))))
  exact ⟨{
    iso := @isoOfDefinableBijection M N Set.univ k A.object C.object F e.equiv.bijective hw
    graph := e.graph }⟩

theorem gammaUniversalObject_admissible (U : GammaRVFiniteObject B k) {i : Fin k}
    (hAd : GammaAdmissible U.toGammaRVObject i) :
    GammaAdmissible (gammaUniversalObject U).toGamma.toGammaRVObject i := ⟨hAd.nonzero,hAd.algebraic⟩

theorem gammaUniversalObject_elementary {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (U : GammaRVFiniteObject B k) (i : Fin k)
    (hAd : GammaAdmissible U.toGammaRVObject i) :
    gammaUniversalObject (gammaFiniteElementaryBasic hκ hs h00 hsmall U i hAd) =
      gammaElementaryAt hκ hs h00 hsmall (gammaUniversalObject U) i (gammaUniversalObject_admissible U hAd) := by
  rfl

end IntegrationInACVF.Section6.FiniteRV
