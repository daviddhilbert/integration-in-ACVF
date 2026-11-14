import Integration7.FixedLabelProductHeadGeometry
import Integration7.ConstantRVLabelSpecialPreparations
import IntegrationSection6.StandardProgramPresentations

/-! Actual two-coordinate standard contraction programs of RV-class
products, with the supplied unary preparation in the second stage and
all fixed old labels retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {b d : ℕ}

theorem head_saturated_rv_class_product
    (A : DefSet (M := M) S 2 0) (B : DefSet (M := M) S 1 0) (r : RV (M := M))
    (hProduct : ∀ p : Point (M := M) 2 0, p ∈ carrier A ↔
      rv (vfAt p 0) = r ∧ ((fun _ : Fin 1 => vfAt p 1),Fin.elim0) ∈ carrier B) :
    HeadSaturated (carrier A) := by
  intro p hp x hx
  have h := (hProduct p).mp hp
  apply (hProduct (replace 0 p x)).mpr
  refine ⟨?_,?_⟩
  · simpa only [replace,vfAt,Function.update_self] using hx.trans h.1
  · simpa only [replace,vfAt,Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)] using h.2

theorem gamma_rv_class_product_tail_preparation_exists
    (A : DefSet (M := M) S 2 0) (B : DefSet (M := M) S 1 0)
    (B' : DefSet (M := M) S 1 b) (T : SpecialBijection B B')
    (hT : GammaChainDefinable P T.chain) (hB' : IsRVPullback (carrier B'))
    (hA : GammaSetDefinable P (carrier A)) (r : RV (M := M))
    (hProduct : ∀ p : Point (M := M) 2 0, p ∈ carrier A ↔
      rv (vfAt p 0) = r ∧ ((fun _ : Fin 1 => vfAt p 1),Fin.elim0) ∈ carrier B)
    (t : Fin d → RV (M := M)) (ht : ∀ i, (t i).val ∈ S)
    (hTuple : DefinableOverBase P (fun _ : Fin d => .rv) {fun i => (t i).val}) :
    Nonempty (ConstantRVLabelSpecialPreparation T (headImage (fixedRVLabelDomain A t ht))
      (Fin.append (fun _ : Fin 1 => r) (Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) t)) P) := by
  let H := headImage (fixedRVLabelDomain A t ht)
  let u := Fin.append (fun _ : Fin 1 => r) (Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) t)
  have hH := gamma_headImage (fixedRVLabelDomain A t ht) (gamma_fixed_rv_label_domain A hA t ht hTuple)
  apply gamma_constant_rv_label_special_preparation_exists T hT hB' H hH u
  · intro p hp
    have h := (head_image_fixed_rv_class_product_carrier A B r hProduct t ht p).mp hp
    have he : retainVFLabels (Fin.elim0 : Fin 0 → Fin (1+(0+d))) p = (p.1,Fin.elim0) :=
      Prod.ext rfl (Subsingleton.elim _ _)
    rw [he]
    exact h.1
  · intro q
    let p : H := ⟨(q.val.1,u),(head_image_fixed_rv_class_product_carrier A B r hProduct t ht _).mpr
      ⟨by
        have he : (show Point (M := M) 1 0 from (q.val.1,Fin.elim0)) = q.val :=
          Prod.ext rfl (Subsingleton.elim _ _)
        exact (congrArg (fun z : Point (M := M) 1 0 => z ∈ carrier B) he).mpr q.property,rfl⟩⟩
    exact ⟨p,Prod.ext rfl (Subsingleton.elim _ _)⟩
  · intro p
    exact ((head_image_fixed_rv_class_product_carrier A B r hProduct t ht p.val).mp p.property).2

def rvClassProductContractionProgram
    (A : DefSet (M := M) S 2 0) (B : DefSet (M := M) S 1 0)
    (B' : DefSet (M := M) S 1 b) (T : SpecialBijection B B')
    (hSat : HeadSaturated (carrier A)) (r : RV (M := M))
    (t : Fin d → RV (M := M)) (ht : ∀ i, (t i).val ∈ S)
    (L : ConstantRVLabelSpecialPreparation T (headImage (fixedRVLabelDomain A t ht))
      (Fin.append (fun _ : Fin 1 => r) (Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) t)) P) :
    OrderedContractionProgram S (fixedRVLabelDomain A t ht) L.head.contractedSet :=
  .step (saturatedIdentityPreparation _ (head_saturated_fixed_rv_labels A hSat t ht)) L.program

theorem gamma_rv_class_product_contraction_program
    (A : DefSet (M := M) S 2 0) (B : DefSet (M := M) S 1 0)
    (B' : DefSet (M := M) S 1 b) (T : SpecialBijection B B')
    (hA : GammaSetDefinable P (carrier A)) (hSat : HeadSaturated (carrier A)) (r : RV (M := M))
    (t : Fin d → RV (M := M)) (ht : ∀ i, (t i).val ∈ S)
    (hTuple : DefinableOverBase P (fun _ : Fin d => .rv) {fun i => (t i).val})
    (L : ConstantRVLabelSpecialPreparation T (headImage (fixedRVLabelDomain A t ht))
      (Fin.append (fun _ : Fin 1 => r) (Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) t)) P) :
    GammaProgramDefinable P (rvClassProductContractionProgram A B B' T hSat r t ht L) := by
  have hH := gamma_fixed_rv_label_domain A hA t ht hTuple
  exact ⟨gamma_identity_graph _ hH,hH,L.program_gamma⟩

def rvClassProductStandardContraction
    (A : DefSet (M := M) S 2 0) (B : DefSet (M := M) S 1 0)
    (B' : DefSet (M := M) S 1 b) (T : SpecialBijection B B')
    (hSat : HeadSaturated (carrier A)) (r : RV (M := M))
    (t : Fin d → RV (M := M)) (ht : ∀ i, (t i).val ∈ S)
    (L : ConstantRVLabelSpecialPreparation T (headImage (fixedRVLabelDomain A t ht))
      (Fin.append (fun _ : Fin 1 => r) (Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) t)) P) :
    StandardContraction (fixedRVLabelDomain A t ht) (Equiv.refl _) :=
  standardFromProgram _ _ (rvClassProductContractionProgram A B B' T hSat r t ht L)
    (vfPermutationImage_id_eq _).symm

end IntegrationInACVF.Section7
