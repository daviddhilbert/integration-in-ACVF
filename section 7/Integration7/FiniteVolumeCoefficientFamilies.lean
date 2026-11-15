import Integration7.MixedRVFactorDomains
import Integration7.NativeCoordinateDensityVolumeObjects
import Integration7.SelectedVolumeFamilies
import Integration7.VolumeFormScalarArithmetic
import Integration7.VolumeFormProducts

/-! A positive constant coefficient times a genuinely finite-label VF
family has a positive selected presentation without inserting a dummy
selected unit coordinate. The density is the actual product density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV carrier)
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a d p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M))
variable (hA : ∀ x : Fin n → VFType (M := M), {r : Fin a → CanonicalRV.RVSort M | (x,r) ∈ A.carrier}.Finite)
variable (ω : VolumeForm A)
variable (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
variable (σ : Fin (p+1) → Fin d) (ε : Fin d)
variable (hR : ∀ t : Fin (p+1) → RV (M := M),
  {r : Fin d → RV (M := M) | (Fin.elim0,r) ∈ carrier R ∧ r ∘ σ=t}.Finite)
variable (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero)

include hA hR in
theorem finite_volume_coefficient_selected_finite (x : Fin n → VFType (M := M))
    (t : Fin (p+1) → CanonicalRV.RVSort M) :
    {r : Fin (a+d) → CanonicalRV.RVSort M |
      (x,r) ∈ (mixedRVFactorDomain A (rawVolumeContractionLabels hc R)).carrier ∧
        r ∘ (Fin.natAdd a ∘ σ)=t}.Finite := by
  apply (((hA x).prod (hR t)).image (fun z => Fin.append z.1 z.2)).subset
  rintro r ⟨hr,ht⟩
  obtain ⟨hLeft,hRight⟩ := (mem_mixed_rv_factor_domain A (rawVolumeContractionLabels hc R) x r).mp hr
  exact ⟨(r ∘ Fin.castAdd d,r ∘ Fin.natAdd a),
    ⟨hLeft,⟨(mem_rawVolumeContractionLabels hc R _).mp hRight,ht⟩⟩,Fin.append_castAdd_natAdd⟩

def finiteVolumeCoefficientFamily : SelectedVFVolumeFamily C n (a+d) p where
  domain := mixedRVFactorDomain A (rawVolumeContractionLabels hc R)
  selected := Fin.natAdd a ∘ σ
  finite_selected := finite_volume_coefficient_selected_finite hc C A hA R σ hR
  form := (ω.prod (nativeCoordinateDensityVolumeObject hc C R σ ε hR hε).form).pullback
    (mixedRVFactorUnpack A (rawVolumeContractionLabels hc R))

theorem finite_volume_coefficient_density
    (δ : Fin a) (hω : ∀ q : A, ω.value q=q.val.2 δ)
    (q : (finiteVolumeCoefficientFamily hc C A hA ω R σ ε hR hε).domain) :
    (finiteVolumeCoefficientFamily hc C A hA ω R σ ε hR hε).form.value q =
      q.val.2 (Fin.natAdd a ε)*q.val.2 (Fin.castAdd d δ) := by
  let z := mixedRVFactorUnpack A (rawVolumeContractionLabels hc R) q
  have hz := mixed_rv_factor_unpack_value A (rawVolumeContractionLabels hc R) q
  change ω.value ⟨z.val.1,z.property.1⟩ * z.val.2 ε = _
  rw [hω]
  change z.val.1.2 δ * z.val.2 ε = _
  rw [hz]
  exact mul_comm _ _
end IntegrationInACVF.Section7
