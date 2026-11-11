import IntegrationSection3ACVF.ResidueReductionSyntax
import IntegrationSection3ACVF.CanonicalModelEquality
import IntegrationSection3ACVF.VFErrorSyntax

/-! The complete graph of affine residue coordinates is LRV-definable.
VF division is eliminated by an existential field variable and a ring
equation, so no inverse symbol is added to the VF language. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4.ResiduePurity
open IntegrationInACVF.Section3

noncomputable section

namespace IntegrationInACVF.Section3ACVF.AffineResidueSyntax

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def graph (a r : VFType (M := M)) : Set (Fin 2 → M) :=
  {z | ∃ u : VFType (M := M), z 0 = (a+r*u).val ∧
    (![u.val,z 1] : Fin 2 → M) ∈ ResidueReductionSyntax.rawGraph (M := M)}

theorem graph_definable (hc : CanonicalStructure.IsCanonical (M := M))
    (a r : VFType (M := M)) : (Set.univ : Set M).Definable LRV (graph a r) := by
  have hErr := VFErrorSyntax.fieldError_definable Set.univ r.val a.val
    (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)
  rw [CanonicalModelEquality.normalize_eq hc] at hErr
  have hEF : (Set.univ : Set M).DefinableFun LRV
      (fun z : Fin 2 ⊕ Fin 1 → M => VFErrorSyntax.fieldError r.val a.val (z (.inr 0)) (z (.inl 0))) :=
    hErr.comp (show (Set.univ : Set M).DefinableMap LRV
      (fun z : Fin 2 ⊕ Fin 1 → M => ![z (.inr 0),z (.inl 0)]) from
        fun i => by fin_cases i <;> exact Set.DefinableFun.proj LRV)
  have hEq := hEF.ofPred_eq (LRV.definableFun_const (Fin 2 ⊕ Fin 1) (Set.mem_univ (iVFZero : M)))
  have hRed := (ResidueReductionSyntax.rawGraph_definable (M := M) Set.univ).preimage_comp
    (![Sum.inr 0,Sum.inl 1] : Fin 2 → Fin 2 ⊕ Fin 1)
  have hV : (Set.univ : Set M).Definable LRV {z : Fin 1 → M | iVF (z 0)} :=
    (definableAt_sort Set.univ .vf).raw_definable
  have hVF := hV.preimage_comp (fun _ : Fin 1 => (Sum.inl 0 : Fin 2 ⊕ Fin 1))
  have hd := (hVF.inter (hEq.inter hRed)).exists_of_finite
  convert hd using 1
  ext z
  change (∃ u : VFType (M := M), z 0 = (a+r*u).val ∧
    (![u.val,z 1] : Fin 2 → M) ∈ ResidueReductionSyntax.rawGraph (M := M)) ↔
    ∃ w : Fin 1 → M, iVF (z 0) ∧
      VFErrorSyntax.fieldError r.val a.val (w 0) (z 0) = iVFZero ∧
        (![w 0,z 1] : Fin 2 → M) ∈ ResidueReductionSyntax.rawGraph (M := M)
  constructor
  · rintro ⟨u,hx,hred⟩
    have hxVF : iVF (z 0) := hx.symm ▸ (a+r*u).property
    let x : VFType (M := M) := ⟨z 0,hxVF⟩
    have hxf : x = a+r*u := Subtype.ext hx
    refine ⟨![u.val],hxVF,?_,hred⟩
    change VFErrorSyntax.fieldError r.val a.val u.val x.val = (0 : VFType (M := M)).val
    rw [VFErrorSyntax.fieldError_vf r a u x]
    apply congrArg Subtype.val
    rw [hxf]
    ring
  · rintro ⟨w,hxVF,herr,hred⟩
    let u : VFType (M := M) := ⟨w 0,hred.1⟩
    let x : VFType (M := M) := ⟨z 0,hxVF⟩
    have he : (x-a-r*u).val = (0 : VFType (M := M)).val :=
      (VFErrorSyntax.fieldError_vf r a u x).symm.trans herr
    have hef : x-a-r*u = 0 := Subtype.ext he
    have hxf : x = a+r*u := by
      calc
        x = (x-a)+a := (sub_add_cancel x a).symm
        _ = r*u+a := congrArg (fun q => q+a) (sub_eq_zero.mp hef)
        _ = a+r*u := add_comm _ _
    exact ⟨u,congrArg Subtype.val hxf,hred⟩

theorem coordinate_iff (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) (x : BallResidueChart.Point a α) (t : ModelResidue M) :
    (![x.val.val,(residueRV t).val] : Fin 2 → M) ∈ graph a r ↔
      t = BallResidueChart.coordinate a r α hr x := by
  have hr0 := BallResidueChart.representative_ne_zero r α hr
  rw [← ResidueReductionSyntax.coordinate_iff a r α hr x t]
  constructor
  · rintro ⟨u,hu,hred⟩
    have hxf : x.val = a+r*u := Subtype.ext hu
    have he : (x.val-a)/r = u := by rw [hxf]; field_simp [hr0]; ring
    simpa only [he,Matrix.cons_val_one,Matrix.cons_val_zero] using hred
  · intro hred
    refine ⟨(x.val-a)/r,?_,hred⟩
    apply congrArg Subtype.val
    field_simp [hr0]
    ring

end IntegrationInACVF.Section3ACVF.AffineResidueSyntax
