module

public import Integration7.NativeUnaryProducts
public import Integration7.FixedLabelProductHeadGeometry
public import IntegrationSection6.StandardProgramPresentations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The native Cartesian rectangle agrees with its fixed-label first
factor presentation, and exchanging its two VF coordinates exchanges
the actual pure unary factors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {d : ℕ}

theorem fixed_native_unary_rectangle (D E : DefSet (M := M) S 1 0)
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ S) :
    fixedRVLabelDomain (nativeUnaryProductDomain D E) z hz =
      nativeUnaryProductDomain (fixedRVLabelDomain D z hz) E := by
  apply defSet_eq_of_carrier_eq
  ext p
  rw [fixed_pure_vf_label_domain_carrier,native_unary_product_carrier,
    native_unary_product_carrier,fixed_pure_vf_label_domain_carrier]
  exact ⟨fun ⟨⟨hD,hE⟩,hz⟩ => ⟨⟨hD,hz⟩,hE⟩,fun ⟨⟨hD,hz⟩,hE⟩ => ⟨⟨hD,hE⟩,hz⟩⟩

theorem swapped_native_unary_rectangle (D E : DefSet (M := M) S 1 0) :
    vfPermutationImage (nativeUnaryProductDomain D E) (Equiv.swap 0 1) = nativeUnaryProductDomain E D := by
  apply defSet_eq_of_carrier_eq
  ext p
  rcases p with ⟨x,t⟩
  rw [vfPermutationImage_row,native_unary_product_carrier,native_unary_product_carrier]
  let p : Point (M := M) 2 0 := (x,t)
  have hLeft : coordinateProject 0 (vfPermutation (Equiv.swap (0 : Fin 2) 1).symm p) =
      (show Point (M := M) 1 0 from ((fun _ : Fin 1 => vfAt p 1),Fin.elim0)) :=
    Prod.ext (by funext i;fin_cases i;rfl) (Subsingleton.elim _ _)
  have hRight : (show Point (M := M) 1 0 from
      ((fun _ : Fin 1 => vfAt (vfPermutation (Equiv.swap (0 : Fin 2) 1).symm p) 1),Fin.elim0)) =
      coordinateProject 0 p := Prod.ext (by funext i;fin_cases i;rfl) (Subsingleton.elim _ _)
  have hD := congrArg (fun q : Point (M := M) 1 0 => q ∈ carrier D) hLeft
  have hE := congrArg (fun q : Point (M := M) 1 0 => q ∈ carrier E) hRight
  exact (and_congr (Iff.of_eq hD) (Iff.of_eq hE)).trans and_comm

end IntegrationInACVF.Section7
