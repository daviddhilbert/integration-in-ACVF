import IntegrationSection6.ParameterCoefficientSemirings
import IntegrationSection6.GammaVFBaseChange

/-! Package the standing model/base hypotheses, and the explicitly
accepted Section5.8 input, for parameterized integration constructions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B C : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ}

structure IntegrationContext (B : Base (M := M)) (κ : Cardinal) (hs : Saturated M κ) where
  countable_le : Cardinal.aleph0 ≤ κ
  characteristic : M ⊨ Axioms.ACVF00
  real_small : Cardinal.mk B.real < κ
  gamma_small : Cardinal.mk B.gamma < κ
  field_base : VFFieldBase B.real
  generated : VFGammaGeneratedBase B
  value : Values.Gamma (M := M)
  value_mem : value ∈ B.gamma
  value_large : 1 < value
  section5_two_order : Section5TwoOrderInputAll countable_le hs

abbrev IntegrationContext.RV (P : IntegrationContext B κ hs) :=
  GlobalIntegrationSemiringTarget P.countable_le hs P.characteristic P.real_small P.field_base P.gamma_small
    P.value P.value_mem P.value_large P.section5_two_order P.generated

@[instance_reducible] def IntegrationContext.vfSemiring (P : IntegrationContext B κ hs) :
    CommSemiring (GammaVFAllAdditiveKPlus B) :=
  gammaVFAllCommSemiring P.countable_le hs P.characteristic P.real_small P.field_base P.gamma_small
    P.value P.value_mem P.value_large P.section5_two_order P.generated

def IntegrationContext.equivalence (P : IntegrationContext B κ hs) :
    letI := P.vfSemiring
    GammaVFAllAdditiveKPlus B ≃+* P.RV :=
  theorem_6_19 P.countable_le hs P.characteristic P.real_small P.field_base P.gamma_small
    P.value P.value_mem P.value_large P.section5_two_order P.generated

def IntegrationContext.atVF (P : IntegrationContext B κ hs) {p : ℕ} (x : Fin p → VF (M := M)) :
    IntegrationContext (vfParameterCoefficientBase B x) κ hs where
  countable_le := P.countable_le
  characteristic := P.characteristic
  real_small := vfParameterCoefficientBase_real_small
    (aleph0_lt_of_small_vf_field_base P.characteristic P.field_base P.real_small) P.real_small P.gamma_small x
  gamma_small := vfParameterCoefficientBase_gamma_small
    (aleph0_lt_of_small_vf_field_base P.characteristic P.field_base P.real_small) P.real_small P.gamma_small x
  field_base := vfParameterCoefficientBase_field x
  generated := vfParameterCoefficientBase_generated P.generated x
  value := P.value
  value_mem := vfParameterCoefficientBase_gamma_contains x P.value_mem
  value_large := P.value_large
  section5_two_order := P.section5_two_order

def integrationContextBaseChange (P : IntegrationContext B κ hs) (Q : IntegrationContext C κ hs)
    (hr : B.real ⊆ C.real) (hg : B.gamma ⊆ C.gamma) :
    letI := P.vfSemiring
    letI := Q.vfSemiring
    GammaVFAllAdditiveKPlus B →+* GammaVFAllAdditiveKPlus C := by
  letI := P.vfSemiring
  letI := Q.vfSemiring
  exact {
    toFun := gammaVFBaseChange hr hg
    map_zero' := map_zero _
    map_add' := map_add _
    map_one' := by
      change gammaVFBaseChange hr hg (PositiveAdditiveGrothendieck.of _ (gammaVFAllUnit B)) =
        PositiveAdditiveGrothendieck.of _ (gammaVFAllUnit C)
      exact gammaVFBaseChange_unit hr hg
    map_mul' := fun a b => by
      change gammaVFBaseChange hr hg (gammaVFProductBilinear a b) =
        gammaVFProductBilinear (gammaVFBaseChange hr hg a) (gammaVFBaseChange hr hg b)
      exact gammaVFBaseChange_product hr hg a b }

def IntegrationContext.scalarMap (P : IntegrationContext B κ hs) {p : ℕ} (x : Fin p → VF (M := M)) :
    P.RV →+* (P.atVF x).RV := by
  letI := P.vfSemiring
  letI := (P.atVF x).vfSemiring
  have hr : B.real ⊆ (vfParameterCoefficientBase B x).real :=
    Set.Subset.trans Set.subset_union_left (subset_closureBase
      (⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ : Base (M := M))).1
  have hg := vfParameterCoefficientBase_gamma_contains (B := B) x
  exact (P.atVF x).equivalence.toRingHom.comp
    ((integrationContextBaseChange P (P.atVF x) hr hg).comp P.equivalence.symm.toRingHom)

end IntegrationInACVF.Section6.FiniteRV
