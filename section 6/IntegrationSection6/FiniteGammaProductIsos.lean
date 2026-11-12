import IntegrationSection6.FiniteGammaProducts
import IntegrationSection6.ProductMapCoordinates
import IntegrationSection6.FiniteGammaAmbientIsos

/-! Cartesian products of actual Gamma-certified finite isomorphisms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k l : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

variable {U U' : GammaObjectAt B S k} {V V' : GammaObjectAt B S l}

theorem gamma_productIso_graph (e : GammaIsoAt U U') (f : GammaIsoAt V V') :
    GammaGraphDefinable B (fun (p : Point (M := M) 0 (rvObjectArity U.object.obj+rvObjectArity V.object.obj))
      (q : Point (M := M) 0 (rvObjectArity U'.object.obj+rvObjectArity V'.object.obj)) =>
        ∃ x : rvObjectDomain (gammaProductAt U V).object.obj,
          x.val = p.2 ∧
          (@rvProductMap M N S k l U.object.obj U'.object.obj V.object.obj V'.object.obj
            (isoAtMap e.iso) (isoAtMap f.iso) x).val = q.2) := by
  have hg := gamma_rv_relation_product e.graph f.graph
  apply GammaGraphDefinable.congr hg
  intro p q
  constructor
  · rintro ⟨⟨u,hu,huv⟩,⟨v,hv,hvv⟩⟩
    let x := @rvPackPair M N S _ _ (rvObjectDomain U.object.obj) (rvObjectDomain V.object.obj) u v
    refine ⟨x,?_,?_⟩
    · change Fin.append u.val v.val = p.2
      rw [hu,hv]
      exact Fin.append_castAdd_natAdd
    · have hh := @rvProductMap_pair_labels M N S k l U.object.obj U'.object.obj V.object.obj V'.object.obj
        (isoAtMap e.iso) (isoAtMap f.iso) u v
      exact hh.trans ((congrArg₂ Fin.append huv hvv).trans Fin.append_castAdd_natAdd)
  · rintro ⟨x,hx,hxv⟩
    obtain ⟨u,v,rfl⟩ := @exists_rvPackPair M N S _ _ (rvObjectDomain U.object.obj) (rvObjectDomain V.object.obj) x
    have hl (j : Fin (rvObjectArity U.object.obj)) := congrFun hx (Fin.castAdd (rvObjectArity V.object.obj) j)
    have hr (j : Fin (rvObjectArity V.object.obj)) := congrFun hx (Fin.natAdd (rvObjectArity U.object.obj) j)
    have hvol := (@rvProductMap_pair_labels M N S k l U.object.obj U'.object.obj V.object.obj V'.object.obj
      (isoAtMap e.iso) (isoAtMap f.iso) u v).symm.trans hxv
    refine ⟨⟨u,?_,?_⟩,⟨v,?_,?_⟩⟩
    · funext j
      exact (Fin.append_left _ _ j).symm.trans (hl j)
    · funext j
      exact (Fin.append_left _ _ j).symm.trans (congrFun hvol (Fin.castAdd (rvObjectArity V'.object.obj) j))
    · funext j
      exact (Fin.append_right _ _ j).symm.trans (hr j)
    · funext j
      exact (Fin.append_right _ _ j).symm.trans (congrFun hvol (Fin.natAdd (rvObjectArity U'.object.obj) j))

def gammaProductIsoAt (e : GammaIsoAt U U') (f : GammaIsoAt V V') :
    GammaIsoAt (gammaProductAt U V) (gammaProductAt U' V') :=
  GammaIsoAt.ofAmbient (@rvProductIso M N S k l U.object.obj U'.object.obj V.object.obj V'.object.obj
    (isoAtAmbient e.iso) (isoAtAmbient f.iso)) (gamma_productIso_graph e f)

end IntegrationInACVF.Section6.FiniteRV
