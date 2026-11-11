import IntegrationSection3ACVF.RVErrorSyntax
import IntegrationSection3ACVF.RealGraphOperations

/-! The actual VF affine error before applying RV. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.VFErrorSyntax

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def fieldError (c fe x y : M) : M :=
  @Term.realize LRV M (CanonicalStructure.normalize (M := M)) _
    (Sum.elim Fin.elim0 ![x,y,iVFZero,c,fe]) RVErrorSyntax.polyTerm

theorem fieldError_vf (c fe x y : VFType (M := M)) :
    fieldError c.val fe.val x.val y.val = (y-fe-c*x).val := by
  have hz : (0 : VFType (M := M)).val = iVFZero := rfl
  simpa only [fieldError,hz,sub_zero] using RVErrorSyntax.poly_value x y 0 c fe

theorem fieldError_definable (S : Set M) (c fe : M)
    (hc : c ∈ S) (hfe : fe ∈ S) (h0 : iVFZero ∈ S) :
    @Set.DefinableFun M LRV (CanonicalStructure.normalize (M := M)) (Fin 2) S
      (fun z => fieldError c fe (z 0) (z 1)) := by
  let E := @fieldError M sM
  let zero := @iVFZero M sM
  let N := @CanonicalStructure.normalize M sM
  change @Set.DefinableFun M LRV N (Fin 2) S (fun z => E c fe (z 0) (z 1))
  letI := N
  have ht : (∅ : Set M).DefinableFun LRV (fun z => Term.realize z RVErrorSyntax.polyTerm) :=
    RVErrorSyntax.polyTerm.definableFun_realize (M := M)
  apply Set.DefinableFun.comp (f := fun z => Term.realize z RVErrorSyntax.polyTerm)
    (g := fun z : Fin 2 → M => Sum.elim Fin.elim0 ![z 0,z 1,zero,c,fe])
  · intro j
    cases j with
    | inl j => exact j.elim0
    | inr j =>
      fin_cases j
      · exact Set.DefinableFun.proj LRV
      · exact Set.DefinableFun.proj LRV
      · exact LRV.definableFun_const (Fin 2) h0
      · exact LRV.definableFun_const (Fin 2) hc
      · exact LRV.definableFun_const (Fin 2) hfe
  · exact ht.of_empty

end IntegrationInACVF.Section3ACVF.VFErrorSyntax
