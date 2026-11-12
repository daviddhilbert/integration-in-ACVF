import Section3.MeanInBalls
import Section3.FieldBase
import Section3.GammaParameters
import Mathlib.Algebra.CharZero.Infinite

/-! A characteristic-zero VF field parameter base is infinite. Smallness
of such a base forces the saturation cardinal strictly above aleph0. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem vfCharZero_of_model00 (h00 : M ⊨ Axioms.ACVF00) : CharZero (Transfer.VFType (M := M)) := by
  apply charZero_of_inj_zero
  intro n hn
  by_contra hn0
  exact Barycentre.natCast_ne_zero h00 n hn0 hn

theorem aleph0_lt_of_small_vf_field_base {B : Base (M := M)} {κ : Cardinal}
    (h00 : M ⊨ Axioms.ACVF00) (F : VFFieldBase B.real) (hsmall : Cardinal.mk B.real < κ) :
    Cardinal.aleph0 < κ := by
  letI : CharZero (Transfer.VFType (M := M)) := vfCharZero_of_model00 h00
  have hF : Cardinal.aleph0 ≤ Cardinal.mk F.field := Cardinal.aleph0_le_mk _
  have hBase : Cardinal.mk F.field ≤ Cardinal.mk B.real :=
    Cardinal.mk_le_of_injective (f := fun x : F.field => (⟨x.val.val,(F.mem_iff x.val).mp x.property⟩ : B.real))
      (by intro x y h; exact Subtype.ext (Subtype.ext (congrArg (fun z : B.real => z.val) h)))
  exact (hF.trans hBase).trans_lt hsmall

end IntegrationInACVF.Section6
