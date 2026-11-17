module

public import Integration7.CoordinateDensityVolumeObjects
public import Integration7.GradedVolumeProducts
public import Integration7.VolumeDensityRescaling
public import Integration7.ContractionRetainedLabelValues
public import Integration7.SmallDimensionContractionNormalization

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A retained constant density label gives exactly the constant-density
volume object. These identities apply to the actual raw and normalized
contraction objects, with no replacement of their label domains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem volume_form_eq_of_value_eq {P : Space LRV M} {A : DefSet P S} {ω π : VolumeForm A}
    (h : ∀ a, ω.value a = π.value a) : ω = π := by
  have hm : ω.map = π.map := by
    apply Map.ext
    intro a
    apply Subtype.ext
    funext i
    have hi : i = 0 := Fin.ext (by have hi := i.isLt;omega)
    subst i
    exact h a
  cases ω
  cases π
  cases hm
  rfl

theorem coordinate_density_eq_constant_volume
    (U : RVFiniteObject (M := M) S (k+1)) (δ : Fin U.obj.arity) (hδ : ∀ u : U.obj.domain, u.val δ ≠ 0)
    (η : CanonicalRV.RVSort M) (hη : η.val ∈ S) (hη0 : η ≠ 0) (hLabel : ∀ u : U.obj.domain, u.val δ = η) :
    coordinateDensityVolumeObject U δ hδ =
      (⟨U,VolumeForm.one _⟩ : PositiveRVVolumeObject (M := M) S k).rescale η hη hη0 := by
  have hForm : (coordinateDensityVolumeObject U δ hδ).form =
      ((⟨U,VolumeForm.one _⟩ : PositiveRVVolumeObject (M := M) S k).rescale η hη hη0).form := by
    apply volume_form_eq_of_value_eq
    intro u
    change u.val δ = η*1
    simpa only [mul_one] using hLabel u
  exact congrArg (fun ω : VolumeForm U.obj.domain => (⟨U,ω⟩ : PositiveRVVolumeObject (M := M) S k)) hForm

open SpecialTransformations.Section5
variable {a : ℕ} {A : SpecialTransformations.Section5.DefSet (M := M) S (k+1) a}
variable {σ : Equiv.Perm (Fin (k+1))}

theorem normalized_contraction_coordinate_density_eq_constant
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : StandardContraction A σ)
    (hF : (canonicalRVObject hc C.contractionObject).volume.FiniteFibres)
    (δ : Fin a) (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0)
    (hLabel : ∀ p : A, p.val.2 δ = η) :
    let U := canonicalNormalizedFiniteContraction hc C hF
    let ε := FiniteRV.contractionOldLabelIndex C δ
    ∃ hε : ∀ u : U.obj.domain, u.val ε ≠ 0,
      coordinateDensityVolumeObject U ε hε = (normalizedUnitVolumeContraction hc C hF).rescale η hη hη0 := by
  intro U ε
  have hValue (u : U.obj.domain) : u.val ε = η :=
    normalized_contraction_retained_label_value C δ η hLabel ⟨u.val,u.property⟩
  have hε : ∀ u : U.obj.domain, u.val ε ≠ 0 := by intro u;rw [hValue];exact hη0
  exact ⟨hε,coordinate_density_eq_constant_volume U ε hε η hη hη0 hValue⟩

theorem raw_contraction_coordinate_density_eq_constant
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : StandardContraction A σ)
    (hF : (canonicalRVObject hc C.contractionObject).volume.FiniteFibres)
    (δ : Fin a) (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0)
    (hLabel : ∀ p : A, p.val.2 δ = η) :
    let U := (rawUnitVolumeContraction hc C hF).underlying
    let ε := suffixIndex C.program.rvArity_le δ
    ∃ hε : ∀ u : U.obj.domain, u.val ε ≠ 0,
      coordinateDensityVolumeObject U ε hε = (rawUnitVolumeContraction hc C hF).rescale η hη hη0 := by
  intro U ε
  have hValue (u : U.obj.domain) : u.val ε = η :=
    raw_contraction_retained_label_value C δ η hLabel ⟨u.val,u.property⟩
  have hε : ∀ u : U.obj.domain, u.val ε ≠ 0 := by intro u;rw [hValue];exact hη0
  exact ⟨hε,coordinate_density_eq_constant_volume U ε hε η hη hη0 hValue⟩

end IntegrationInACVF.Section7
