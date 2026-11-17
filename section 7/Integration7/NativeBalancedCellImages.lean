module

public import Integration7.NativeVFPairImages
public import Integration7.BalancedCellTranslationEquivalences

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual native coordinate translations of a balanced two-cell
have precisely the two product images from the paper's opposite orders. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.BalancedFibres
open IntegrationInACVF.Section4.Cells

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {D E : Set (VF (M := M))} {f : VF (M := M) → VF (M := M)} {r t : RV (M := M)}

theorem balanced_vertical_native_centre_independent
    (A : DefSet (M := M) S 2 0)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hCentre : ∀ p : A, (c p).val 0 = f (p.val.1 0))
    (p q : A) (he : erase (1 : Fin 2) p.val = erase 1 q.val) : (c p).val 0 = (c q).val 0 := by
  have h0 := congrArg (fun z => z.1 (0 : Fin 2)) he
  simp only [erase,replace,Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)] at h0
  exact (hCentre p).trans ((congrArg f h0).trans (hCentre q).symm)

theorem balanced_vertical_native_image
    (A : DefSet (M := M) S 2 0)
    (h : HasBalancedFibres D E (nativeVFPairDomain A) f r t)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hCentre : ∀ p : A, (c p).val 0 = f (p.val.1 0)) :
    nativeVFPairDomain (relativeTranslationImage A 1 c) = D ×ˢ {z : VF (M := M) | rv z = t} := by
  let e := (balancedVerticalTranslationEquiv h).trans (Equiv.Set.prod D {z : VF (M := M) | rv z = t}).symm
  apply native_vf_pair_map_image A (relativeTranslationMap A 1 c) _ e
  intro p
  change ((relativeTranslationMap A 1 c p).val.1 0,(relativeTranslationMap A 1 c p).val.1 1) =
    (p.val.1 0,(show VFType (M := M) from p.val.1 1)-f (p.val.1 0))
  rw [relative_translation_map_value]
  simp only [replace,Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1),Function.update_self,hCentre]

theorem balanced_horizontal_native_centre_independent
    (A : DefSet (M := M) S 2 0)
    (h : HasBalancedFibres D E (nativeVFPairDomain A) f r t)
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hCentre : ∀ p : A, (c p).val 0 =
      ((balancedPositionEquiv h).symm ⟨p.val.1 1,(h.subset ⟨p.val,p.property,rfl⟩).2⟩).val)
    (p q : A) (he : erase (0 : Fin 2) p.val = erase 0 q.val) : (c p).val 0 = (c q).val 0 := by
  have h1 := congrArg (fun z => z.1 (1 : Fin 2)) he
  simp only [erase,replace,Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)] at h1
  have hb : (⟨p.val.1 1,(h.subset ⟨p.val,p.property,rfl⟩).2⟩ : E) =
      ⟨q.val.1 1,(h.subset ⟨q.val,q.property,rfl⟩).2⟩ := Subtype.ext h1
  exact (hCentre p).trans ((congrArg (fun z : E => ((balancedPositionEquiv h).symm z).val) hb).trans (hCentre q).symm)

theorem balanced_horizontal_native_image
    (A : DefSet (M := M) S 2 0)
    (h : HasBalancedFibres D E (nativeVFPairDomain A) f r t)
    (hD : IntegrationInACVF.Section3ACVF.PaperBalls.IsOpenBall (rawSet D))
    (c : Map A (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S))
    (hCentre : ∀ p : A, (c p).val 0 =
      ((balancedPositionEquiv h).symm ⟨p.val.1 1,(h.subset ⟨p.val,p.property,rfl⟩).2⟩).val) :
    nativeVFPairDomain (relativeTranslationImage A 0 c) = {z : VF (M := M) | rv z = r} ×ˢ E := by
  let e := (balancedHorizontalTranslationEquiv h hD).trans (Equiv.Set.prod {z : VF (M := M) | rv z = r} E).symm
  apply native_vf_pair_map_image A (relativeTranslationMap A 0 c) _ e
  intro p
  change ((relativeTranslationMap A 0 c p).val.1 0,(relativeTranslationMap A 0 c p).val.1 1) =
    ((show VFType (M := M) from p.val.1 0)-((balancedPositionEquiv h).symm ⟨p.val.1 1,(h.subset ⟨p.val,p.property,rfl⟩).2⟩).val,p.val.1 1)
  rw [relative_translation_map_value]
  simp only [replace,Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0),Function.update_self,hCentre]

end IntegrationInACVF.Section7
