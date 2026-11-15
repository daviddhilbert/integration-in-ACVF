import Integration7.CoordinateSelectedCoefficientFamilies
import Integration7.IndependentRVProductDensityGraphs
import Integration7.NativeCoordinateDensityVolumeObjects

/-! Literal-coordinate coefficients admit actual constrained unary
special preparations on the density graph of their genuine family
product. The old and coefficient label projections stay literal. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a b d k p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (F : SelectedVFVolumeFamily C 1 a k)
variable (R : DefSet (M := M) (C.base : Set M) 0 d)
variable (σ : Fin (p+1) → Fin d) (ε : Fin d)
variable (hR : ∀ t : Fin (p+1) → RV (M := M),
  {r : Fin d → RV (M := M) | (Fin.elim0,r) ∈ carrier R ∧ r ∘ σ=t}.Finite)
variable (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero)

def nativeCoordinateCoefficientFamily : SelectedVFVolumeFamily C 1 (a+d) ((p+1)+k) :=
  coordinateSelectedCoefficientFamily F (nativeCoordinateDensityVolumeObject hc C R σ ε hR hε) σ (fun _ => rfl)

theorem native_coordinate_coefficient_density (δ : Fin a)
    (hF : ∀ q : F.domain, F.form.value q=q.val.2 δ)
    (q : (nativeCoordinateCoefficientFamily hc C F R σ ε hR hε).domain) :
    (nativeCoordinateCoefficientFamily hc C F R σ ε hR hε).form.value q =
      q.val.2 (Fin.natAdd a ε)*q.val.2 (Fin.castAdd d δ) :=
  coordinate_selected_coefficient_density F (nativeCoordinateDensityVolumeObject hc C R σ ε hR hε) σ
    (fun _ => rfl) δ ε hF (fun _ => rfl) q

variable (Ξ : Set (Values.Gamma (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))

theorem native_coordinate_coefficient_density_graph_source (δ : Fin a)
    (hF : ∀ q : F.domain, F.form.value q=q.val.2 δ) :
    nativeMixedVolumeDomain hc (nativeCoordinateCoefficientFamily hc C F R σ ε hR hε).densityGraph.domain =
      constrainedUnarySource C Ξ hNames (nativeMixedVolumeDomain hc F.domain)
        (independentRVDensityConstraint hc C Ξ hNames R δ ε) (Fin.castAdd 1 ∘ Fin.castAdd d) :=
  independent_rv_product_density_graph_source hc C Ξ hNames R δ ε F.domain _
    (native_coordinate_coefficient_density hc C F R σ ε hR hε δ hF)

theorem native_coordinate_coefficient_special_preparation_exists (δ : Fin a)
    (hF : ∀ q : F.domain, F.form.value q=q.val.2 δ)
    {B : DefSet (M := M) (C.base : Set M) 1 b}
    (T : SpecialBijection (nativeMixedVolumeDomain hc F.domain) B)
    (hT : GammaChainDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.chain)
    (hB : IsRVPullback (carrier B)) :
    Nonempty (RVLabelConstraintSpecialPreparation T
      (nativeMixedVolumeDomain hc (nativeCoordinateCoefficientFamily hc C F R σ ε hR hε).densityGraph.domain)
      (independentRVDensityConstraint hc C Ξ hNames R δ ε) (Fin.castAdd 1 ∘ Fin.castAdd d)
      (⟨(C.base : Set M),Ξ⟩ : Base (M := M))) := by
  rw [native_coordinate_coefficient_density_graph_source hc C F R σ ε hR hε Ξ hNames δ hF]
  exact constrained_unary_special_preparation_exists C Ξ hNames T hT hB _ _
end IntegrationInACVF.Section7
