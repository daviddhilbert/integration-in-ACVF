import IntegrationSection4.FiniteRVScalarImage
import Section5.GammaLiftRelation
import Section3.GammaSupport

/-! A scalar definable function has finite VF image when every input VF
coordinate is fixed and only its RV labels vary. Fixed VF values are
internal finite parameters; the original-base smallness scope is retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}

def fixedVFInsertMap (S : Set M) (x : Fin n → VF (M := M))
    (hx : ∀ i, (x i).val ∈ S) :
    Map (PresentedSet.univ (pointSpace (M := M) 0 m) S)
      (PresentedSet.univ (pointSpace n m) S) :=
  Map.ofCodes _ (fun p => (x,p.2))
    (fun z => Sum.elim (fun i => (x i).val) (fun i => z (.inr i)))
    (by
      intro j
      cases j with
      | inl j =>
        letI := @CanonicalStructure.normalize M sM
        exact LRV.definableFun_const _ (hx j)
      | inr j => exact rawProj S (.inr j : Fin 0 ⊕ Fin m))
    (by intro c; exact ⟨fun j => (x j).property,c.property.2⟩)
    (by intro c; refine Prod.ext ?_ rfl
        funext j; apply Subtype.ext; rfl)

theorem fixed_vf_scalar_image_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (D : Set (Point (M := M) n m))
    (g : D → VF (M := M))
    (hg : GammaScalarGraphDefinable G (fun p y => ∃ a : D, a.val = p ∧ g a = y))
    (x : Fin n → VF (M := M)) :
    {y : VF (M := M) | ∃ a : D, a.val.1 = x ∧ g a = y}.Finite := by
  let H : GammaParameters.Base (M := M) := ⟨G.real ∪ Set.range (fun i => (x i).val),G.gamma⟩
  have hHsmall : Cardinal.mk H.real < κ := small_union_range hκ G.real hsmall (fun i => (x i).val)
  have hgH : GammaScalarGraphDefinable H (fun p y => ∃ a : D, a.val = p ∧ g a = y) :=
    GammaParameters.DefinableOverBase.mono hg Set.subset_union_left Set.Subset.rfl
  let F := fixedVFInsertMap (m := m) H.real x (fun i => Or.inr ⟨i,rfl⟩)
  let I := Map.id (PresentedSet.univ (pointSpace (M := M) 1 0) H.real)
  let r (u : Point (M := M) 0 m) (v : Point (M := M) 1 0) : Prop :=
    ∃ a : D, a.val = (F ⟨u,Set.mem_univ _⟩).val ∧ g a = vfAt v 0
  have hr : GammaGraphDefinable H r := hgH.preimage_maps F I
  have hSingle (u : Point (M := M) 0 m) (v w : Point (M := M) 1 0)
      (hv : r u v) (hw : r u w) : vfAt v 0 = vfAt w 0 := by
    obtain ⟨a,ha,hav⟩ := hv
    obtain ⟨b,hb,hbw⟩ := hw
    have hab : a = b := Subtype.ext (ha.trans hb.symm)
    exact hav.symm.trans ((congrArg g hab).trans hbw)
  have hFin := IntegrationInACVF.Section4.FiniteRVScalarImage.finite_image hκ hs H hHsmall r hr hSingle
  apply hFin.subset
  rintro y ⟨a,ha,rfl⟩
  let u : Point (M := M) 0 m := (Fin.elim0,a.val.2)
  let v : Point (M := M) 1 0 := (fun _ => g a,Fin.elim0)
  refine ⟨u,v,⟨a,?_,rfl⟩,rfl⟩
  exact Prod.ext ha rfl

end IntegrationInACVF.Section5
