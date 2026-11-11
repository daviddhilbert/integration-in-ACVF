import IntegrationSection4.GammaOffsets
import Section3.GammaBaseFiniteImage

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5

namespace IntegrationInACVF.Section4.FiniteRVScalarImage

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

local notation "N" => (@CanonicalStructure.normalize M sM)

/-- An original-base RV-to-VF scalar graph has finite image. -/
theorem finite_image {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (G : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk G.real < κ) {l : ℕ}
    (r : Point (M := M) 0 l → Point (M := M) 1 0 → Prop)
    (hr : GammaGraphDefinable G r)
    (hSingle : ∀ u v w, r u v → r u w → vfAt v 0 = vfAt w 0) :
    {x : VF (M := M) | ∃ u v, r u v ∧ vfAt v 0 = x}.Finite := by
  obtain ⟨d,t,hReal⟩ := hr.real_specialize
  let S := G.real ∪ Set.range (rawTuple t)
  have hS : Cardinal.mk S < κ := small_union_range hκ G.real hsmall (rawTuple t)
  let P := pointSpace (M := M) 0 l
  let Q := pointSpace (M := M) 1 0
  let π : (Fin 0 ⊕ Fin l) ⊕ (Fin 1 ⊕ Fin 0) → Fin l ⊕ Fin 1 :=
    Sum.elim (Sum.elim Fin.elim0 Sum.inl) (Sum.elim Sum.inr Fin.elim0)
  let R : Set ((Fin l → M) × M) :=
    {p | (Sum.elim p.1 ![p.2]) ∘ π ∈ (@SpecialTransformations.DefinableGeometry.Space.relation LRV M N P Q r)}
  have hRaw : @RawClosure.Tuple.RelationDefinable M (CanonicalStructure.normalize (M := M)) l S R := by
    have h := @Set.Definable.preimage_comp M S LRV (CanonicalStructure.normalize (M := M))
      _ _ π _ hReal
    change @Set.Definable M S LRV N (Fin l ⊕ Fin 1) _
    convert h using 1
    ext z
    have he : Sum.elim (z ∘ Sum.inl) ![z (.inr 0)] ∘ π = z ∘ π := by
      funext i
      rcases i with (i|i)|(i|i)
      · exact i.elim0
      · rfl
      · fin_cases i; rfl
      · exact i.elim0
    exact iff_of_eq (congrArg (fun x => x ∈ (@SpecialTransformations.DefinableGeometry.Space.relation LRV M N P Q r)) he)
  have hSort (u : Fin l → M) (x : M) (h : (u,x) ∈ R) :
      (∀ i, @iRV M (CanonicalStructure.normalize (M := M)) (u i)) ∧
        @iVF M (CanonicalStructure.normalize (M := M)) x := by
    obtain ⟨hp,hq,_⟩ := h
    exact ⟨fun i => hp.2 i,hq.1 0⟩
  have hFin (u : Fin l → M) : {x | (u,x) ∈ R}.Finite := by
    apply Set.Subsingleton.finite
    intro x hx y hy
    obtain ⟨hp,hq,hx⟩ := hx
    obtain ⟨hp',hq',hy⟩ := hy
    have heP : (@SpecialTransformations.DefinableGeometry.Space.decode LRV M N P) ⟨(Sum.elim u ![x] ∘ π) ∘ Sum.inl,hp⟩ =
        (@SpecialTransformations.DefinableGeometry.Space.decode LRV M N P) ⟨(Sum.elim u ![y] ∘ π) ∘ Sum.inl,hp'⟩ := by
      apply Prod.ext
      · exact Subsingleton.elim _ _
      · funext i; apply Subtype.ext; rfl
    rw [← heP] at hy
    exact congrArg Subtype.val (hSingle _ _ _ hx hy)
  have hF := @finite_rv_to_vf_relation_image M (CanonicalStructure.normalize (M := M))
    (CanonicalStructure.normalized_model hM) CanonicalStructure.normalize_isCanonical κ hs.normalize
    S hS l R hRaw hSort hFin
  have hCover : {x : VF (M := M) | ∃ u v, r u v ∧ vfAt v 0 = x} ⊆
      Subtype.val ⁻¹' {x | ∃ u, (u,x) ∈ R} := by
    rintro x ⟨u,v,huv,hvx⟩
    let ucode : Fin l → M := fun i => (u.2 i).val
    have hp : (Sum.elim ucode ![x.val] ∘ π) ∘ Sum.inl ∈ (@SpecialTransformations.DefinableGeometry.Space.domain LRV M N P) :=
      ⟨(by intro i; exact i.elim0),fun i => (u.2 i).property⟩
    have hq : (Sum.elim ucode ![x.val] ∘ π) ∘ Sum.inr ∈ (@SpecialTransformations.DefinableGeometry.Space.domain LRV M N Q) :=
      ⟨(by intro i; fin_cases i; exact x.property),(by intro i; exact i.elim0)⟩
    refine ⟨ucode,hp,hq,?_⟩
    have heP : (@SpecialTransformations.DefinableGeometry.Space.decode LRV M N P) ⟨_,hp⟩ = u := by
      apply Prod.ext
      · exact Subsingleton.elim _ _
      · rfl
    have heQ : (@SpecialTransformations.DefinableGeometry.Space.decode LRV M N Q) ⟨_,hq⟩ = v := by
      apply Prod.ext
      · funext i; fin_cases i; exact hvx.symm
      · exact Subsingleton.elim _ _
    rwa [heP,heQ]
  exact (hF.preimage Subtype.val_injective.injOn).subset hCover

end IntegrationInACVF.Section4.FiniteRVScalarImage
