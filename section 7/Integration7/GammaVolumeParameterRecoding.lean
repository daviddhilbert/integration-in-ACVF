import Integration7.GammaVolumeRowAgreements
import Integration7.ZeroAuxVolumeWitnesses
import IntegrationSection6.GammaRecodingAgreements

/-! Recode full coordinate-and-density formulas to a new parameter
block. The density retains explicit nonvanishing on every formula row. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p q a k : ℕ} {sp : Fin p → SortTag} {sq : Fin q → SortTag}

structure GammaVolumeParameterRecode (B : Base (M := M)) (p q : ℕ)
    (sp : Fin p → SortTag) (sq : Fin q → SortTag) where
  formulas : GammaParameterRecode B p q sp sq

def GammaVolumeParameterRecode.volumeObject (C : GammaVolumeParameterRecode B p q sp sq)
    (F : GammaRVVolumeSchema B p a k sp) : GammaRVVolumeSchema B q a k sq where
  object := C.formulas.object F.object
  density := nonzeroDensityFormula (C.formulas.relation ⟨F.density,F.density_definable⟩).val
  density_definable := nonzeroDensityFormula_definable (C.formulas.relation ⟨F.density,F.density_definable⟩).property
  density_nonzero _ hw := hw.2

theorem GammaVolumeParameterRecode.volumeObject_bound (C : GammaVolumeParameterRecode B p q sp sq)
    (F : GammaRVVolumeSchema B p a k sp) : (C.volumeObject F).object.bound = F.object.bound := rfl

def GammaVolumeParameterRecode.VolumeObjectAgreement (C : GammaVolumeParameterRecode B p q sp sq)
    (F : GammaRVVolumeSchema B p a k sp) (z : Fin p → M) (t : Fin q → M) : Prop :=
  C.formulas.ObjectAgreement F.object z t ∧ C.formulas.RelationAgreement ⟨F.density,F.density_definable⟩ z t

theorem GammaVolumeParameterRecode.volumeObject_rows (C : GammaVolumeParameterRecode B p q sp sq)
    (F : GammaRVVolumeSchema B p a k sp) (z : Fin p → M) (t : Fin q → M)
    (h : C.VolumeObjectAgreement F z t) : GammaVolumeRowAgreement F z (C.volumeObject F) t := by
  refine ⟨h.1,h.1.1,?_⟩
  intro x ω
  change (Fin.append (Fin.append z x) ω ∈ F.density) ↔
    (Fin.append (Fin.append t x) ω ∈ nonzeroDensityFormula (C.formulas.relation ⟨F.density,F.density_definable⟩).val)
  rw [nonzeroDensityFormula_append]
  constructor
  · intro hρ
    refine ⟨(h.2 x ω).mp hρ,?_⟩
    have hn := F.density_nonzero _ hρ
    change Fin.append (Fin.append z x) ω (Fin.natAdd (p+a) (0 : Fin 1)) ≠ iRVZero at hn
    simpa only [Fin.append_right] using hn
  · exact fun hρ => (h.2 x ω).mpr hρ.1

theorem GammaVolumeParameterRecode.volumeObject_valid (C : GammaVolumeParameterRecode B p q sp sq)
    (F : GammaRVVolumeSchema B p a k sp) (z : Fin p → M) (t : Fin q → M)
    (ht : ∀ i, sortEval (sq i) (t i)) (h : C.VolumeObjectAgreement F z t) (hF : F.valid z) :
    (C.volumeObject F).valid t := (C.volumeObject_rows F z t h).valid ht rfl hF

end IntegrationInACVF.Section7
