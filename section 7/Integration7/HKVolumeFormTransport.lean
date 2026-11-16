module

public import Integration7.VolumeFormScalarArithmetic
public import Integration7.VolumeDensityRescaling

@[expose] public section

/-! Multiplying the source and target forms by corresponding definable
weights preserves the actual positive volume isomorphism. The multiplier
may vary over the labels; it need not be a named constant. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def multiplyForm (U : PositiveRVVolumeObject (M := M) S k)
    (ρ : VolumeForm U.underlying.obj.domain) : PositiveRVVolumeObject (M := M) S k :=
  ⟨U.underlying, ρ.mul U.form⟩

set_option allowUnsafeReducibility true in
attribute [local reducible] multiplyForm

@[simp] theorem multiplyForm_density (U : PositiveRVVolumeObject (M := M) S k)
    (ρ : VolumeForm U.underlying.obj.domain) (u : U.underlying.obj.domain) :
    (multiplyForm U ρ).form.value u = ρ.value u * U.form.value u := rfl

theorem multiplyForm_ratio {U V : PositiveRVVolumeObject (M := M) S k}
    (e : U.essential ≅ V.essential)
    (ρ : VolumeForm U.underlying.obj.domain) (σ : VolumeForm V.underlying.obj.domain)
    (hρ : ∀ u : U.essential.obj.domain,
      ρ.value ⟨u.val, rvEssentialLabels_subset U.underlying.obj u.property⟩ =
      σ.value ⟨(finiteIsoMap e u).val,
        rvEssentialLabels_subset V.underlying.obj (finiteIsoMap e u).property⟩)
    (u : U.essential.obj.domain) :
    volumeRatio (multiplyForm U ρ) (multiplyForm V σ) e u = volumeRatio U V e u := by
  change (ρ.value ⟨u.val, rvEssentialLabels_subset U.underlying.obj u.property⟩ * U.essentialForm.value u) /
    (σ.value ⟨(finiteIsoMap e u).val,
      rvEssentialLabels_subset V.underlying.obj (finiteIsoMap e u).property⟩ *
      V.essentialForm.value (finiteIsoMap e u)) = _
  rw [← hρ u]
  exact mul_div_mul_left _ _ (ρ.nonzero _)

def multiplyFormIso {U V : PositiveRVVolumeObject (M := M) S k}
    (f : RVVolumeIso U V)
    (ρ : VolumeForm U.underlying.obj.domain) (σ : VolumeForm V.underlying.obj.domain)
    (hρ : ∀ u : U.essential.obj.domain,
      ρ.value ⟨u.val, rvEssentialLabels_subset U.underlying.obj u.property⟩ =
      σ.value ⟨(finiteIsoMap f.iso u).val,
        rvEssentialLabels_subset V.underlying.obj (finiteIsoMap f.iso u).property⟩) :
    RVVolumeIso (multiplyForm U ρ) (multiplyForm V σ) where
  iso := f.iso
  gamma u := gammaVolumeEquation_of_absoluteRatio _ u (by
    rw [multiplyForm_ratio f.iso ρ σ hρ]
    exact f.absolute_volumeRatio u)
  rv := f.rv.mono (fun u hu => by
    rw [multiplyForm_ratio f.iso ρ σ hρ]
    exact hu)

end IntegrationInACVF.Section7.HK
