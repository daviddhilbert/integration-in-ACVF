import IntegrationSection4.RVLabelAttachment
import IntegrationSection4.FamilyRefinementDomains

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.GammaRVMap

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem attachment_labels {G : GammaParameters.Base (M := M)} {n m d : ℕ}
    {A : Set (Point (M := M) n m)} (P : GammaRVMap G A d) (a : A) :
    (fun i => ((attachment P a).2 i).val) =
      Fin.append (fun i => (a.val.2 i).val) (fun i => (P.toFun a i).val) := by
  funext i
  cases i using Fin.addCases with
  | left i => simp only [attachment,Fin.append_left]
  | right i => simp only [attachment,Fin.append_right]

def refinementPoint {m d : ℕ} (G : GammaParameters.Base (M := M))
    (A : (Fin m → M) → Set M) (e : (Fin m → M) → M → Fin d → M)
    (he : FamilyPositionRefinement.RVRefinement (GammaBaseBridge.fullBase G) A e)
    (a : GammaFamilySyntax.domain A) :
    GammaFamilySyntax.domain (FamilyRefinementDomains.domain A e) :=
  ⟨attachment (fromRefinement G A e he) a,by
    let P := fromRefinement G A e he
    have hLabels : (fun i => ((attachment P a).2 i).val) =
        Fin.append (GammaFamilySyntax.labels a.val) (e (GammaFamilySyntax.labels a.val) (vfAt a.val 0).val) := by
      rw [attachment_labels]
      rfl
    change (vfAt a.val 0).val ∈ FamilyRefinementDomains.domain A e (fun i => ((attachment P a).2 i).val)
    rw [hLabels]
    exact FamilyRefinementDomains.lift_mem A e _ _ a.property⟩

theorem refinementPoint_graph {m d : ℕ} (G : GammaParameters.Base (M := M))
    (A : (Fin m → M) → Set M) (e : (Fin m → M) → M → Fin d → M)
    (he : FamilyPositionRefinement.RVRefinement (GammaBaseBridge.fullBase G) A e) :
    GammaGraphDefinable G (fun (p : Point (M := M) 1 m) (q : Point (M := M) 1 (m+d)) =>
      ∃ a : GammaFamilySyntax.domain A, a.val = p ∧ (refinementPoint G A e he a).val = q) :=
  attachment_graph (fromRefinement G A e he)

theorem refinementPoint_surjective {m d : ℕ} (G : GammaParameters.Base (M := M))
    (A : (Fin m → M) → Set M) (e : (Fin m → M) → M → Fin d → M)
    (he : FamilyPositionRefinement.RVRefinement (GammaBaseBridge.fullBase G) A e) :
    Function.Surjective (refinementPoint G A e he) := by
  intro b
  let q : Point (M := M) 1 m := (b.val.1,b.val.2 ∘ Fin.castAdd d)
  have hMem : (vfAt b.val 0).val ∈ A (GammaFamilySyntax.labels q) ∧
      (fun i => (b.val.2 (Fin.natAdd m i)).val) =
        e (GammaFamilySyntax.labels q) (vfAt b.val 0).val := b.property
  let a : GammaFamilySyntax.domain A := ⟨q,hMem.1⟩
  refine ⟨a,Subtype.ext (Prod.ext rfl (funext fun i => ?_))⟩
  cases i using Fin.addCases with
  | left i =>
    change Fin.append a.val.2 ((fromRefinement G A e he).toFun a) (Fin.castAdd d i) = b.val.2 (Fin.castAdd d i)
    rw [Fin.append_left]
    rfl
  | right i =>
    change Fin.append a.val.2 ((fromRefinement G A e he).toFun a) (Fin.natAdd m i) = b.val.2 (Fin.natAdd m i)
    rw [Fin.append_right]
    apply Subtype.ext
    exact (congrFun hMem.2 i).symm

theorem refinementPoint_reflects_rv {m d : ℕ} (G : GammaParameters.Base (M := M))
    (A : (Fin m → M) → Set M) (e : (Fin m → M) → M → Fin d → M)
    (he : FamilyPositionRefinement.RVRefinement (GammaBaseBridge.fullBase G) A e)
    (a b : GammaFamilySyntax.domain A)
    (h : SameRV (refinementPoint G A e he a).val (refinementPoint G A e he b).val) :
    SameRV a.val b.val := by
  obtain ⟨hv,hl⟩ := (sameRV_iff _ _).mp h
  apply (sameRV_iff _ _).mpr
  refine ⟨hv,funext fun i => ?_⟩
  have hh := congrFun hl (Fin.castAdd d i)
  change Fin.append a.val.2 ((fromRefinement G A e he).toFun a) (Fin.castAdd d i) =
    Fin.append b.val.2 ((fromRefinement G A e he).toFun b) (Fin.castAdd d i) at hh
  simpa only [Fin.append_left] using hh

end IntegrationInACVF.Section4.GammaRVMap
