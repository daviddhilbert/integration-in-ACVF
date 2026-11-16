module

public import Integration7.NativeRVProductVolumeCharts
public import Integration7.FactoredHeadRetainedLabels

@[expose] public section

/-! Functional RV graph labels are compatible with the actual full
volume product chart of a unary head. The coefficient and fibre densities
are the original retained labels, and source finiteness is derived. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a b l d p k : ℕ}
variable {P : Base (M := M)}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable {A : DefSet (M := M) (C.base : Set M) 1 a} {B : DefSet (M := M) (C.base : Set M) 1 b}
variable {T : SpecialBijection A B} {H : DefSet (M := M) (C.base : Set M) 1 l}
variable {Q : DefSet (M := M) (C.base : Set M) 0 l} {ρ : Fin a → Fin l}
variable (L : RVLabelConstraintSpecialPreparation T H Q ρ P)
variable (R : DefSet (M := M) (C.base : Set M) 0 d)
variable (Φ : Map Q (PresentedSet.prod (PresentedSet.univ (pointSpace (M := M) 0 a) (C.base : Set M)) R))
variable (hΦ : Function.Bijective Φ) (hOld : ∀ q : Q, (Φ q).val.1.2=q.val.2 ∘ ρ)
variable (χ : Fin d → Fin l) (hCoef : ∀ q : Q, (Φ q).val.2.2=q.val.2 ∘ χ)
variable (σ : Fin (p+1) → Fin d) (τ : Fin (k+1) → Fin (1+b)) (δ : Fin d) (ε : Fin (1+b))
variable (hR : ∀ t : Fin (p+1) → RV (M := M), {r : Fin d → RV (M := M) | (Fin.elim0,r) ∈ carrier R ∧ r ∘ σ=t}.Finite)
variable (hB : ∀ t : Fin (k+1) → RV (M := M), {r : Fin (1+b) → RV (M := M) | (Fin.elim0,r) ∈ carrier (headImage B) ∧ r ∘ τ=t}.Finite)
variable (hδ : ∀ q : R, (q.val.2 δ).val ≠ iRVZero)
variable (hε : ∀ q : headImage B, (q.val.2 ε).val ≠ iRVZero)

include hCoef in
private theorem coefficient_values (q : headImage L.target) :
    (L.factoredHeadProductMap R Φ q).val.1.2=q.val.2 ∘ (L.headParameters ∘ χ) := by
  change (Φ (L.headParameterMap q)).val.2.2=q.val.2 ∘ (L.headParameters ∘ χ)
  rw [hCoef]
  rfl

def factoredHeadProductVolumeObject :=
  nativeRVProductVolumeChart hc C (headImage L.target) R (headImage B) (L.factoredHeadProductMap R Φ)
    (L.factored_head_product_map_bijective R Φ hΦ hOld) (L.headParameters ∘ χ) L.headProjection
    (coefficient_values C L R Φ χ hCoef) (fun _ => rfl) σ τ δ ε hR hB hδ hε

def factoredHeadProductVolumeIso :
    RVVolumeIso (factoredHeadProductVolumeObject hc C L R Φ hΦ hOld χ hCoef σ τ δ ε hR hB hδ hε)
      ((nativeCoordinateDensityVolumeObject hc C R σ δ hR hδ).prod
        (nativeCoordinateDensityVolumeObject hc C (headImage B) τ ε hB hε)) :=
  nativeRVProductVolumeChartIso hc C (headImage L.target) R (headImage B) (L.factoredHeadProductMap R Φ)
    (L.factored_head_product_map_bijective R Φ hΦ hOld) (L.headParameters ∘ χ) L.headProjection
    (coefficient_values C L R Φ χ hCoef) (fun _ => rfl) σ τ δ ε hR hB hδ hε

theorem factored_head_product_volume_density
    (u : (factoredHeadProductVolumeObject hc C L R Φ hΦ hOld χ hCoef σ τ δ ε hR hB hδ hε).underlying.obj.domain) :
    (factoredHeadProductVolumeObject hc C L R Φ hΦ hOld χ hCoef σ τ δ ε hR hB hδ hε).form.value u =
      u.val (L.headParameters (χ δ)) * u.val (L.headProjection ε) :=
  native_rv_product_volume_chart_density hc C (headImage L.target) R (headImage B) (L.factoredHeadProductMap R Φ)
    (L.factored_head_product_map_bijective R Φ hΦ hOld) (L.headParameters ∘ χ) L.headProjection
    (coefficient_values C L R Φ χ hCoef) (fun _ => rfl) σ τ δ ε hR hB hδ hε u

theorem factored_head_product_volume_original_density
    (ε₀ : Fin a)
    (hε₀ : ∀ q : headImage B, (q.val.2 (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) ε₀))).val ≠ iRVZero)
    (u : (factoredHeadProductVolumeObject hc C L R Φ hΦ hOld χ hCoef σ τ δ
      (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) ε₀)) hR hB hδ hε₀).underlying.obj.domain) :
    (factoredHeadProductVolumeObject hc C L R Φ hΦ hOld χ hCoef σ τ δ
      (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le T.chain) ε₀)) hR hB hδ hε₀).form.value u =
      u.val (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le L.special.chain) (χ δ))) *
      u.val (Fin.natAdd 1 (suffixIndex (special_chain_rvArity_le L.special.chain) (ρ ε₀))) := by
  rw [factored_head_product_volume_density]
  let q : headImage L.target := ⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc _ u.val).mp u.property⟩
  exact congrArg₂ (fun x y => x*y) (L.carried_head_suffix q (χ δ)) (L.prepared_head_suffix q ε₀)
end IntegrationInACVF.Section7
