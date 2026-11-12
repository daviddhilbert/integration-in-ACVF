import IntegrationSection6.GammaRVProductRelations
import IntegrationSection6.GammaRVRealSets
import IntegrationSection6.FiniteGammaObjects
import Section4.RVFiniteHomogeneousProducts

/-! Products in the requested finite-volume categories retain full
original-Gamma domain and volume graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k l : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gamma_product_volume (U : GammaObjectAt B S k) (V : GammaObjectAt B S l) :
    GammaGraphDefinable B (fun (p : Point (M := M) 0 (rvObjectArity U.object.obj+rvObjectArity V.object.obj))
      (q : Point (M := M) 0 (k+l)) =>
        ∃ x : rvObjectDomain (@rvProductObject M N S k l U.object.obj V.object.obj),
          x.val = p.2 ∧ (rvObjectVolume (@rvProductObject M N S k l U.object.obj V.object.obj) x).val = q.2) := by
  have hg := gamma_rv_relation_product U.volume_graph V.volume_graph
  apply GammaGraphDefinable.congr hg
  intro p q
  constructor
  · rintro ⟨⟨u,hu,huv⟩,⟨v,hv,hvv⟩⟩
    let x := @rvPackPair M N S _ _ (rvObjectDomain U.object.obj) (rvObjectDomain V.object.obj) u v
    refine ⟨x,?_,?_⟩
    · change Fin.append u.val v.val = p.2
      rw [hu,hv]
      exact Fin.append_castAdd_natAdd
    · have h := @rvProductObject_value_pair M N S k l U.object.obj V.object.obj u v
      change (@RVObject.value M N S (k+l) (@rvProductObject M N S k l U.object.obj V.object.obj) x) = q.2
      rw [h]
      change Fin.append _ _ = q.2
      change (@RVObject.value M N S k U.object.obj u) = (fun j => q.2 (Fin.castAdd l j)) at huv
      change (@RVObject.value M N S l V.object.obj v) = (fun j => q.2 (Fin.natAdd k j)) at hvv
      rw [huv,hvv]
      exact Fin.append_castAdd_natAdd
  · rintro ⟨x,hx,hxv⟩
    obtain ⟨u,v,rfl⟩ := @exists_rvPackPair M N S _ _ (rvObjectDomain U.object.obj) (rvObjectDomain V.object.obj) x
    have hl (j : Fin (rvObjectArity U.object.obj)) := congrFun hx (Fin.castAdd (rvObjectArity V.object.obj) j)
    have hr (j : Fin (rvObjectArity V.object.obj)) := congrFun hx (Fin.natAdd (rvObjectArity U.object.obj) j)
    have hvol := (@rvProductObject_value_pair M N S k l U.object.obj V.object.obj u v).symm.trans hxv
    refine ⟨⟨u,?_,?_⟩,⟨v,?_,?_⟩⟩
    · funext j
      exact (Fin.append_left _ _ j).symm.trans (hl j)
    · funext j
      exact (Fin.append_left _ _ j).symm.trans (congrFun hvol (Fin.castAdd l j))
    · funext j
      exact (Fin.append_right _ _ j).symm.trans (hr j)
    · funext j
      exact (Fin.append_right _ _ j).symm.trans (congrFun hvol (Fin.natAdd k j))

def gammaProductAt (U : GammaObjectAt B S k) (V : GammaObjectAt B S l) : GammaObjectAt B S (k+l) where
  object := @rvFiniteProductObject M N S k l U.object V.object
  real_contains := U.real_contains
  domain_graph := gamma_rv_product_domain (rvObjectDomain U.object.obj) (rvObjectDomain V.object.obj)
    U.domain_graph V.domain_graph
  volume_graph := gamma_product_volume U V

end IntegrationInACVF.Section6.FiniteRV
