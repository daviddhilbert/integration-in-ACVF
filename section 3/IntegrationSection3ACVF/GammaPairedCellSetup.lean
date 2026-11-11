import IntegrationSection3ACVF.GammaPiecewiseMonotonicity
import IntegrationSection3ACVF.GammaOrderCellSyntax
import IntegrationSection3ACVF.GammaFunctionSets
import IntegrationSection3ACVF.FiniteOrderCommonControls

/-! Source and target endpoint sets for a definable Gamma bijection.
Source cells are monotone; every target cell has constant membership in
each actual image of a source cell. All controllers are constructed. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section3ACVF.GammaPairedCellSetup

open FullGammaSyntax FiniteOrderCells FiniteOrderCellPartition

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem exists_controllers {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (a b : Values.Gamma (M := M)) (J : Set (Values.Gamma (M := M)))
    (f : Values.Gamma (M := M) → Values.Gamma (M := M))
    (hG : Definable B (GammaFunctionSyntax.graph (Set.Icc a b) f))
    (hBij : Set.BijOn f (Set.Icc a b) J) :
    ∃ F G : Finset (Values.Gamma (M := M)),
      a ∈ F ∧ b ∈ F ∧ FiniteOrder.Controls F (Set.Icc a b) ∧
      (∀ c : Index F (Set.Icc a b), StrictMonoOn f (cell F c.val) ∨ StrictAntiOn f (cell F c.val)) ∧
      (∀ x ∈ F, x ∈ Set.Icc a b → f x ∈ G) ∧ FiniteOrder.Controls G J ∧
      (∀ c : Index F (Set.Icc a b), FiniteOrder.Controls G (f '' cell F c.val)) := by
  classical
  obtain ⟨F0,hF0⟩ := GammaPiecewiseMonotonicity.exists_cuts hκ hs h00 B hsmall _ f hG hBij.2.1
  let F := insert a (insert b F0)
  have haF : a ∈ F := Finset.mem_insert_self _ _
  have hbF : b ∈ F := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hF0Sub : F0 ⊆ F := fun _ hx => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
  have hCellMono (c : Index F (Set.Icc a b)) : StrictMonoOn f (cell F c.val) ∨ StrictAntiOn f (cell F c.val) := by
    apply monotone_on_cell F (Set.Icc a b) f _ c
    intro l u hlu hAvoid hSub
    exact hF0 l u hlu (fun x hx hxF0 => hAvoid x hx (hF0Sub hxF0)) hSub
  have hImageControl (c : Index F (Set.Icc a b)) : ∃ H, FiniteOrder.Controls H (f '' cell F c.val) := by
    let C := GammaTupleParameters.extend B (fun t : F => t.val)
    have hGC : Definable C (GammaFunctionSyntax.graph (Set.Icc a b) f) :=
      GammaTupleParameters.mono B (fun t : F => t.val) hG
    have hC := GammaOrderCellSyntax.cell_definable B F c.val
    have hImage := GammaFunctionSets.image_definable C (Set.Icc a b) (cell F c.val) f hGC hC c.property.2
    exact FullGammaControllers.finite_controller h00 C _ hImage
  have hD := GammaFunctionSyntax.domain_definable B _ f hG
  have hJ : Scalar B J := by
    have hd := GammaFunctionSets.image_definable B (Set.Icc a b) (Set.Icc a b) f hG hD Set.Subset.rfl
    rwa [hBij.image_eq] at hd
  obtain ⟨H,hH⟩ := FullGammaControllers.finite_controller h00 B J hJ
  let E := (F.filter (· ∈ Set.Icc a b)).image f ∪ H
  obtain ⟨G,hEG,hGControl⟩ := FiniteOrderCommonControls.exists_common
    (fun c : Index F (Set.Icc a b) => f '' cell F c.val) hImageControl E
  refine ⟨F,G,haF,hbF,controls_Icc F a b haF hbF,hCellMono,?_,?_,hGControl⟩
  · intro x hx hxD
    exact hEG (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,hxD⟩,rfl⟩))
  · apply controls_mono (G := G) (hF := hH)
    intro x hx
    exact hEG (Finset.mem_union_right _ hx)

end IntegrationInACVF.Section3ACVF.GammaPairedCellSetup
