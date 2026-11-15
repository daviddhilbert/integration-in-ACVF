import Integration7.IndependentHeadVolumeProductCharts
import Integration7.AllDegreeVolumeClasses
import Integration7.VolumeBlowupClasses

/-! The actual independent head product chart gives finite selected
fibres and the exact common-blowup product class. All densities and
coordinate selectors are the ones of the two supplied actual factors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {a b d p k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable {A : DefSet (M := M) (C.base : Set M) 1 a} {B : DefSet (M := M) (C.base : Set M) 1 b}
variable {T : SpecialBijection A B} {H : DefSet (M := M) (C.base : Set M) 1 (a+d)}
variable {Q : DefSet (M := M) (C.base : Set M) 0 (a+d)}
variable (L : RVLabelConstraintSpecialPreparation T H Q (Fin.castAdd d) P)
variable (R : DefSet (M := M) (C.base : Set M) 0 d)
variable (hQ : ∀ q : Point (M := M) 0 (a+d), q ∈ carrier Q ↔ (Fin.elim0,q.2 ∘ Fin.natAdd a) ∈ carrier R)
variable (σ : Fin (p+1) → Fin d) (τ : Fin (k+1) → Fin (1+b)) (δ : Fin d) (ε : Fin (1+b))
variable (hR : ∀ t : Fin (p+1) → RV (M := M), {r : Fin d → RV (M := M) | (Fin.elim0,r) ∈ carrier R ∧ r ∘ σ=t}.Finite)
variable (hB : ∀ t : Fin (k+1) → RV (M := M), {r : Fin (1+b) → RV (M := M) | (Fin.elim0,r) ∈ carrier (headImage B) ∧ r ∘ τ=t}.Finite)
variable (hδ : ∀ q : R, (q.val.2 δ).val ≠ iRVZero)
variable (hε : ∀ q : headImage B, (q.val.2 ε).val ≠ iRVZero)

include hc R hQ δ ε hR hB hδ hε in
theorem independent_head_product_selected_fibres_finite
    (t : Fin (((p+1)+k)+1) → RV (M := M)) :
    {r : Fin (1+L.arity) → RV (M := M) | (Fin.elim0,r) ∈ carrier (headImage L.target) ∧
      r ∘ Fin.append (L.headParameters ∘ Fin.natAdd a ∘ σ) (L.headProjection ∘ τ)=t}.Finite := by
  let U := independentHeadProductVolumeObject hc C L R hQ σ τ δ ε hR hB hδ hε
  apply ((U.underlying.property ⟨t,Set.mem_univ _⟩).image Subtype.val).subset
  rintro r ⟨hr,he⟩
  refine ⟨⟨r,(mem_rawVolumeContractionLabels hc _ r).mpr hr⟩,?_,rfl⟩
  exact Subtype.ext he

theorem independent_head_product_volume_class :
    positiveVolumeBlowupClass hc C (independentHeadProductVolumeObject hc C L R hQ σ τ δ ε hR hB hδ hε) =
      rvVolumeBlowupClassesProduct hc C (p+1) (k+1)
        (positiveVolumeBlowupClass hc C (nativeCoordinateDensityVolumeObject hc C R σ δ hR hδ))
        (positiveVolumeBlowupClass hc C (nativeCoordinateDensityVolumeObject hc C (headImage B) τ ε hB hε)) :=
  positiveVolumeBlowupClass_iso hc C (independentHeadProductVolumeIso hc C L R hQ σ τ δ ε hR hB hδ hε)

theorem independent_head_product_volume_iso_gamma
    (hBase : (C.base : Set M) = (Substructure.closure LRV P.real : Set M)) :
    (independentHeadProductVolumeIso hc C L R hQ σ τ δ ε hR hB hδ hε).GammaDefinable P :=
  (independentHeadProductVolumeIso hc C L R hQ σ τ δ ε hR hB hδ hε).gamma_of_term_context hc C hBase
end IntegrationInACVF.Section7
