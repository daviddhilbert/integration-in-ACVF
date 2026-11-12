import IntegrationSection6.SmallGammaDefinableClosure
import Section3.GeneratedBaseLifting
import Section3.GammaDefinableClosureField
import Section3.FieldBase
import Section5.GammaLift

/-! The actual dcl(B,x) coefficient bases in6.20: generation, the field
convention and smallness follow from the original standing hypotheses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p : ℕ}

theorem gammaBase_eq_of_components {B C : Base (M := M)}
    (hr : B.real = C.real) (hg : B.gamma = C.gamma) : B = C := by
  cases B
  cases C
  cases hr
  cases hg
  rfl

def closureBase_field (B : Base (M := M)) : VFFieldBase (closureBase B).real where
  field := vfDefinableClosureFieldBase B
  mem_iff x := by
    constructor
    · intro hx
      exact ⟨.vf,hx⟩
    · rintro ⟨σ,hx⟩
      have he : σ = .vf := CanonicalStructure.sort_unique hM
        (hx.proper x.val (Set.mem_singleton _)) x.property
      cases he
      exact hx

theorem generated_closure_real_extension (hB : VFGammaGeneratedBase B)
    (X : Set M) (hX : ∀ x ∈ X, iVF x) :
    VFGammaGeneratedBase (closureBase (⟨B.real ∪ X,B.gamma⟩ : Base (M := M))) := by
  obtain ⟨A,G,hAB,hGB,hA,hgen⟩ := hB
  let D : Base (M := M) := ⟨A ∪ X,G⟩
  let C : Base (M := M) := ⟨B.real ∪ X,B.gamma⟩
  have hBC := closureBase_mono (B := (⟨A,G⟩ : Base (M := M))) (C := D)
    Set.subset_union_left (Set.Subset.refl _)
  rw [hgen] at hBC
  have hCDreal : C.real ⊆ (closureBase D).real := by
    rintro x (hx | hx)
    · exact hBC.1 hx
    · exact (subset_closureBase D).1 (Or.inr hx)
  have hback := closureBase_mono hCDreal hBC.2
  rw [closureBase_idempotent] at hback
  have hforward := closureBase_mono (B := D) (C := C)
    (Set.union_subset (hAB.trans Set.subset_union_left) Set.subset_union_right) hGB
  have he : closureBase D = closureBase C :=
    gammaBase_eq_of_components (Set.Subset.antisymm hforward.1 hback.1)
      (Set.Subset.antisymm hforward.2 hback.2)
  refine ⟨A ∪ X,G,?_,?_,?_,he⟩
  · exact (Set.union_subset (hAB.trans Set.subset_union_left) Set.subset_union_right).trans (subset_closureBase C).1
  · exact hGB.trans (subset_closureBase C).2
  · rintro x (hx | hx)
    · exact hA x hx
    · exact hX x hx

def vfParameterCoefficientBase (B : Base (M := M)) (x : Fin p → VF (M := M)) : Base (M := M) :=
  closureBase ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩

theorem vfParameterCoefficientBase_generated (hB : VFGammaGeneratedBase B) (x : Fin p → VF (M := M)) :
    VFGammaGeneratedBase (vfParameterCoefficientBase B x) :=
  generated_closure_real_extension hB _ (by rintro z ⟨j,rfl⟩; exact (x j).property)

def vfParameterCoefficientBase_field (x : Fin p → VF (M := M)) : VFFieldBase (vfParameterCoefficientBase B x).real :=
  closureBase_field _

theorem vfParameterCoefficientBase_real_small {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ) (x : Fin p → VF (M := M)) :
    Cardinal.mk (vfParameterCoefficientBase B x).real < κ :=
  closureBase_real_small hκ _ (small_union_range hκ.le B.real hr (fun j => (x j).val)) hg

theorem vfParameterCoefficientBase_gamma_small {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ) (x : Fin p → VF (M := M)) :
    Cardinal.mk (vfParameterCoefficientBase B x).gamma < κ :=
  closureBase_gamma_small hκ _ (small_union_range hκ.le B.real hr (fun j => (x j).val)) hg

theorem vfParameterCoefficientBase_gamma_contains (x : Fin p → VF (M := M)) :
    B.gamma ⊆ (vfParameterCoefficientBase B x).gamma :=
  (subset_closureBase (⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ : Base (M := M))).2

end IntegrationInACVF.Section6
