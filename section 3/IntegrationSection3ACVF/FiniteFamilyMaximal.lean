import IntegrationSection3ACVF.FiniteFamilyCoordinates

/-! Finite-family coordinate fibres are actual intrinsic maximal open
balls, and the finite scalar bookkeeping has the actual component and
total-hole counts. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open scoped BigOperators
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4.ResiduePurity
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF.PuncturedGeometry
open IntegrationInACVF.Section3ACVF.ThinFamilyGeometry
open IntegrationInACVF.Section3ACVF.ThinResidueCoordinates

noncomputable section

namespace IntegrationInACVF.Section3ACVF.FiniteFamilyMaximal

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem counts (F : Finset (PuncturedBall M)) (C : ∀ d : F, Chart d.val)
    (e : F ↪ ModelResidue M) :
    (FiniteTaggedHoles.tags e).card = F.card ∧
      (FiniteTaggedHoles.holes e (fun d => (C d).excluded)).card = ∑ d : F, d.val.holes.card := by
  constructor
  · simpa only [Fintype.card_coe] using FiniteTaggedHoles.tags_card e
  · rw [FiniteTaggedHoles.holes_card]
    exact Finset.sum_congr rfl (fun i _ => (C i).card_eq)

theorem fibre_maximal (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (F : Finset (PuncturedBall M)) (C : ∀ d : F, Chart d.val)
    (e : F ↪ ModelResidue M)
    (hDis : (F : Set (PuncturedBall M)).Pairwise (fun d e => Disjoint d.body e.body))
    (x : M) (hx : x ∈ body F) :
    MaximalOpenClasses.IsMaximal (body F)
      (OpenToOpenQuotient.fibre (body F) (FiniteFamilyCoordinates.value F C e)
        (FiniteFamilyCoordinates.value F C e x)) := by
  obtain ⟨d,hd,hxd⟩ := hx
  let i : F := ⟨d,hd⟩
  rw [FiniteFamilyCoordinates.fibre_component F C e hDis i x hxd,
    ThinResidueCoordinates.fibre_ball (C i) x hxd]
  let j := ResidueBallClasses.ball (C i).a (C i).r (C i).α (C i).hr (ThinResidueCoordinates.value (C i) x)
  let b := (ResidueBallClasses.centre (C i).a (C i).r (C i).α (C i).hr
    (ThinResidueCoordinates.value (C i) x)).val
  have hjU : BallImaginaries.underlying j = GammaRadiusAtomicity.gammaBall b (C i).α true :=
    ResidueBallClasses.underlying_ball _ _ _ _ _
  have hSub : BallImaginaries.underlying j ⊆ d.body := by
    rw [← ThinResidueCoordinates.fibre_ball (C i) x hxd]
    exact fun y hy => hy.1
  have hj : j ∈ MaximalSubballGeometry.classes d (C i).α :=
    ⟨⟨Or.inr ⟨b,(C i).α,hjU⟩,Or.inr (Or.inr ⟨b,(C i).α,true,hjU,rfl⟩)⟩,hSub⟩
  have hThin (k : PuncturedBall M) (hk : k ∈ F) : IsThin k :=
    ⟨(C ⟨k,hk⟩).a,(C ⟨k,hk⟩).α,(C ⟨k,hk⟩).parent_eq,(C ⟨k,hk⟩).holes_eq⟩
  exact MaximalOpenClasses.class_maximal δ hδ F hThin hDis d hd (C i).a (C i).α
    (C i).parent_eq j hj

end IntegrationInACVF.Section3ACVF.FiniteFamilyMaximal
