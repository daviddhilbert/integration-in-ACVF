import IntegrationSection4.RefinementAttachment
import IntegrationSection4.SpecialRVFibres

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5

namespace IntegrationInACVF.Section4.GammaRVMap

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def preparedRefinement {m d l : ℕ} (G : GammaParameters.Base (M := M))
    (A : (Fin m → M) → Set M) (e : (Fin m → M) → M → Fin d → M)
    (he : FamilyPositionRefinement.RVRefinement (GammaBaseBridge.fullBase G) A e)
    {E : Set (Point (M := M) 1 l)}
    (T : GammaSpecialBijection G (GammaFamilySyntax.domain (FamilyRefinementDomains.domain A e)) E) :
    GammaRVMap G (GammaFamilySyntax.domain A) (1+l) :=
  (fromSpecial T).precomp (refinementPoint G A e he) (refinementPoint_graph G A e he)

theorem preparedRefinement_reflects_rv {m d l : ℕ} (G : GammaParameters.Base (M := M))
    (A : (Fin m → M) → Set M) (e : (Fin m → M) → M → Fin d → M)
    (he : FamilyPositionRefinement.RVRefinement (GammaBaseBridge.fullBase G) A e)
    {E : Set (Point (M := M) 1 l)}
    (T : GammaSpecialBijection G (GammaFamilySyntax.domain (FamilyRefinementDomains.domain A e)) E)
    (a b : GammaFamilySyntax.domain A)
    (h : (preparedRefinement G A e he T).toFun a = (preparedRefinement G A e he T).toFun b) :
    SameRV a.val b.val :=
  refinementPoint_reflects_rv G A e he a b
    (fromSpecial_reflects_rv T (refinementPoint G A e he a) (refinementPoint G A e he b) h)

/-- After RV refinement and special preparation, the actual old-domain
RV-map fibre is exactly one inverse VF body with the old RV context fixed. -/
theorem preparedRefinement_fibre {m d l : ℕ} (G : GammaParameters.Base (M := M))
    (A : (Fin m → M) → Set M) (e : (Fin m → M) → M → Fin d → M)
    (he : FamilyPositionRefinement.RVRefinement (GammaBaseBridge.fullBase G) A e)
    {E : Set (Point (M := M) 1 l)}
    (T : GammaSpecialBijection G (GammaFamilySyntax.domain (FamilyRefinementDomains.domain A e)) E)
    (a₀ : GammaFamilySyntax.domain A) :
    {p | ∃ a : GammaFamilySyntax.domain A, a.val = p ∧
      (preparedRefinement G A e he T).toFun a = (preparedRefinement G A e he T).toFun a₀} =
    {p | (vfAt p 0).val ∈ InverseBodies.body T.special
      (T.special.toMap (specialSource T (refinementPoint G A e he a₀))) ∧ p.2 = a₀.val.2} := by
  let H := refinementPoint G A e he
  let Q := preparedRefinement G A e he T
  let b := T.special.toMap (specialSource T (H a₀))
  have hRow := fromSpecial_fibre T (H a₀)
  have hOld (a : GammaFamilySyntax.domain A) (i : Fin m) :
      (H a).val.2 (Fin.castAdd d i) = a.val.2 i := by
    change Fin.append a.val.2 ((fromRefinement G A e he).toFun a) (Fin.castAdd d i) = _
    exact Fin.append_left _ _ i
  ext p
  constructor
  · rintro ⟨a,rfl,hValue⟩
    have hh := (Set.ext_iff.mp hRow (H a).val).mp ⟨H a,rfl,hValue⟩
    refine ⟨hh.1,funext fun i => ?_⟩
    rw [T.special.inverse_apply] at hh
    have hl := congrFun hh.2 (Fin.castAdd d i)
    simpa only [specialSource,hOld] using hl
  · rintro ⟨hp,hLabels⟩
    let q : Point (M := M) 1 (m+d) := (p.1,(H a₀).val.2)
    have hq : (vfAt q 0).val ∈ InverseBodies.body T.special b ∧
        q.2 = (T.special.inverseMap b).val.2 := by
      refine ⟨hp,?_⟩
      rw [T.special.inverse_apply]
      rfl
    obtain ⟨c,hc,hValue⟩ := (Set.ext_iff.mp hRow q).mpr hq
    obtain ⟨a,ha⟩ := refinementPoint_surjective G A e he c
    have hPoint : (H a).val = q := (congrArg Subtype.val ha).trans hc
    have hap : a.val = p := by
      apply Prod.ext
      · exact congrArg (fun q : Point (M := M) 1 (m+d) => q.1) hPoint
      · funext i
        have hh := congrFun (congrArg Prod.snd hPoint) (Fin.castAdd d i)
        change (H a).val.2 (Fin.castAdd d i) = (H a₀).val.2 (Fin.castAdd d i) at hh
        rw [hOld,hOld] at hh
        exact hh.trans (congrFun hLabels i).symm
    refine ⟨a,hap,?_⟩
    change (fromSpecial T).toFun (H a) = (fromSpecial T).toFun (H a₀)
    change H a = c at ha
    rw [ha]
    exact hValue

end IntegrationInACVF.Section4.GammaRVMap
