import IntegrationSection5.GammaGraphRawBridge
import Section3.GammaBaseFiniteImage

/-! A definable unary map has finite VF output at every fixed VF input, even as its RV labels vary. The checked RV-to-VF finite-image theorem is applied over finite original-base support plus that input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {P : GammaParameters.Base (M := M)} {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

theorem unary_vf_fibre_image_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (f : Map A B) (hf : GammaGraphDefinable P (pointMapGraph f)) (x : VF (M := M)) :
    {y : M | ∃ a : A, vfAt a.val 0 = x ∧ (vfAt (f a).val 0).val = y}.Finite := by
  classical
  have hGraph := unaryTupleMap_graph f hf
  obtain ⟨T,hT,hG⟩ := @ImaginaryParameters.OverBase.specialize LRV M
    (@CanonicalStructure.normalize M sM) _ _ inferInstance _ _ _ inferInstance _ hGraph
  let C := P.real ∪ T
  let D := C ∪ Set.range (![x.val] : Fin 1 → M)
  have hCsmall : Cardinal.mk C < κ := small_union_finite hκ P.real hsmall T hT
  have hDsmall : Cardinal.mk D < κ := small_union_range hκ C hCsmall (![x.val] : Fin 1 → M)
  let G := FiniteTupleGraphs.graph (pointValues '' carrier A) (unaryTupleMap f)
  have hGD : @Set.Definable M D LRV (@CanonicalStructure.normalize M sM) _ G :=
    by
      letI := @CanonicalStructure.normalize M sM
      exact hG.mono Set.subset_union_left
  let F : ((Fin m ⊕ Fin 1) ⊕ Fin l → M) →
      ((Fin 1 ⊕ Fin m) ⊕ (Fin 1 ⊕ Fin l) → M) := fun z =>
    Sum.elim (Sum.elim (fun _ => x.val) (fun j => z (.inl (.inl j))))
      (Sum.elim (fun _ => z (.inl (.inr 0))) (fun j => z (.inr j)))
  have hF : @Set.DefinableMap M LRV (@CanonicalStructure.normalize M sM) _ _ D F := by
    letI := @CanonicalStructure.normalize M sM
    intro i
    cases i with
    | inl i =>
      cases i with
      | inl i => exact LRV.definableFun_const _ (Or.inr ⟨0,rfl⟩)
      | inr i => exact Set.DefinableFun.proj LRV
    | inr i =>
      cases i with
      | inl i => exact Set.DefinableFun.proj LRV
      | inr i => exact Set.DefinableFun.proj LRV
  have hH := @Set.Definable.preimage_map M LRV (@CanonicalStructure.normalize M sM)
    D _ _ inferInstance F hF G hGD
  have hRaw := @Set.Definable.exists_of_finite M D LRV (@CanonicalStructure.normalize M sM)
    (Fin m ⊕ Fin 1) (Fin l) inferInstance _ hH
  let R : Set ((Fin m → M) × M) :=
    {p | ∃ a : A, vfAt a.val 0 = x ∧ (fun j => (a.val.2 j).val) = p.1 ∧ (vfAt (f a).val 0).val = p.2}
  have hR : @RawClosure.Tuple.RelationDefinable M (@CanonicalStructure.normalize M sM) m D R := by
    unfold RawClosure.Tuple.RelationDefinable
    convert hRaw using 1
    ext z
    change (∃ a : A, vfAt a.val 0 = x ∧ (fun j => (a.val.2 j).val) = z ∘ Sum.inl ∧
      (vfAt (f a).val 0).val = z (.inr 0)) ↔ ∃ s : Fin l → M, F (Sum.elim z s) ∈ G
    constructor
    · rintro ⟨a,hx,ht,hy⟩
      refine ⟨fun j => ((f a).val.2 j).val,?_,?_⟩
      · refine ⟨a.val,a.property,?_⟩
        funext i
        cases i with
        | inl i =>
          have hi : i = 0 := Subsingleton.elim _ _
          subst i
          exact congrArg Subtype.val hx
        | inr i => exact congrFun ht i
      · have hSrc : F (Sum.elim z (fun j => ((f a).val.2 j).val)) ∘ Sum.inl = pointValues a.val := by
          funext i
          cases i with
          | inl i =>
            have hi : i = 0 := Subsingleton.elim _ _
            subst i
            exact (congrArg Subtype.val hx).symm
          | inr i => exact (congrFun ht i).symm
        rw [hSrc,unaryTupleMap_apply f a]
        funext i
        cases i with
        | inl i =>
          have hi : i = 0 := Subsingleton.elim _ _
          subst i
          exact hy.symm
        | inr i => rfl
    · rintro ⟨s,⟨p,hp,he⟩,hout⟩
      let a : A := ⟨p,hp⟩
      have hx : vfAt p 0 = x := Subtype.ext (congrFun he (.inl 0))
      have ht : (fun j => (p.2 j).val) = z ∘ Sum.inl := by
        funext j
        exact congrFun he (.inr j)
      rw [← he,unaryTupleMap_apply f a] at hout
      exact ⟨a,hx,ht,(congrFun hout (.inl 0)).symm⟩
  have hSort : ∀ t b, (t,b) ∈ R → (∀ j, @iRV M (@CanonicalStructure.normalize M sM) (t j)) ∧
      @iVF M (@CanonicalStructure.normalize M sM) b := by
    rintro t b ⟨a,hx,ht,hy⟩
    refine ⟨?_,?_⟩
    · intro j
      have he : (a.val.2 j).val = t j := congrFun ht j
      rw [← he]
      exact (a.val.2 j).property
    · have he : (vfAt (f a).val 0).val = b := hy
      rw [← he]
      exact (vfAt (f a).val 0).property
  have hFinite : ∀ t, {y | (t,y) ∈ R}.Finite := by
    intro t
    apply Set.Subsingleton.finite
    rintro y ⟨a,hax,hat,hay⟩ z ⟨b,hbx,hbt,hbz⟩
    have hab : a = b := by
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        exact hax.trans hbx.symm
      · funext i
        exact Subtype.ext (congrFun (hat.trans hbt.symm) i)
    subst b
    exact hay.symm.trans hbz
  have hImage := @finite_rv_to_vf_relation_image M (@CanonicalStructure.normalize M sM)
    (CanonicalStructure.normalized_model hM) CanonicalStructure.normalize_isCanonical κ hs.normalize
    D hDsmall m R hR hSort hFinite
  apply hImage.subset
  rintro y ⟨a,hx,hy⟩
  exact ⟨fun j => (a.val.2 j).val,a,hx,rfl,hy⟩
end IntegrationInACVF.Section5
