import Integration7.GammaCoefficientNativeObjects
import Integration7.GammaFieldUnaryPreparations
import Integration7.CoordinateCoefficientContractionProductCharts
import Integration7.GammaFunPositiveCoefficients
import Integration7.UnarySpecialStandardContractions
import Integration7.GammaFunZeroCoefficients
import Integration7.GammaDefinableFamilies

/-! **Gamma coefficient charts for unary families.** Coordinate-selected coefficient families of
Gamma families by Gamma coefficients are Gamma; a Gamma special preparation of a retained unary
family lifts to its native coefficient family over the same Gamma base; and the contraction chart
of the coefficient family as coefficient times prepared head is Gamma-definable. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV carrier headImage SpecialBijection GammaChainDefinable GammaSetDefinable
  GammaFocusDefinable)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {G P P' : Base (M := M)} {S : Set M}
variable {n a b d k p l r : ℕ}

theorem gamma_chain_mono (hr : P.real ⊆ P'.real) (hg : P.gamma ⊆ P'.gamma)
    {A : SpecialTransformations.Section5.DefSet (M := M) S n a}
    {D : SpecialTransformations.Section5.DefSet (M := M) S n b}
    (T : SpecialTransformations.Section5.Chain S n A D) (hT : GammaChainDefinable P T) :
    GammaChainDefinable P' T := by
  induction T with
  | nil A => exact hT.mono hr hg
  | cons f tail ih =>
    refine ⟨?_,ih hT.2⟩
    cases f with
    | canonical A => exact hT.1.mono hr hg
    | centripetal D => exact ⟨hT.1.1.mono hr hg,hT.1.2.1.mono hr hg,hT.1.2.2.mono hr hg⟩

/-- Change the Gamma base of a label-constraint special preparation to a larger one. -/
def RVLabelConstraintSpecialPreparation.monoBase
    {A : SpecialTransformations.Section5.DefSet (M := M) S 1 a}
    {B : SpecialTransformations.Section5.DefSet (M := M) S 1 b} {T : SpecialBijection A B}
    {l : ℕ} {H : SpecialTransformations.Section5.DefSet (M := M) S 1 l}
    {Q : SpecialTransformations.Section5.DefSet (M := M) S 0 l} {ρ : Fin a → Fin l}
    (L : RVLabelConstraintSpecialPreparation T H Q ρ P) (hr : P.real ⊆ P'.real) (hg : P.gamma ⊆ P'.gamma) :
    RVLabelConstraintSpecialPreparation T H Q ρ P' :=
  { L with gamma := gamma_chain_mono hr hg _ L.gamma }

/-- Coordinate-selected coefficient families of Gamma data are Gamma. -/
theorem SelectedVFVolumeFamily.Gamma.coordinateSelectedCoefficient (hc : CanonicalStructure.IsCanonical (M := M))
    {C : BaseContext M} {F : SelectedVFVolumeFamily C n a k} (hF : F.Gamma G)
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) p} (hU : VolumeObjectGamma U G)
    (σ : Fin (p+1) → Fin U.underlying.obj.arity)
    (hσ : ∀ u : U.underlying.obj.domain, U.underlying.obj.value u = u.val ∘ σ) :
    (coordinateSelectedCoefficientFamily F U σ hσ).Gamma G :=
  ⟨gamma_mixed_rv_factor_domain hF.domain hU.domain_graph,
    density_graph_of_volume_form_graph _ (gamma_mixed_rv_factor_form_graph hc F.form U.form hF.domain
      hU.domain_graph (volume_form_graph_of_density_graph F.form hF.densityGraph) hU.density)⟩

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

/-- A Gamma special preparation of a retained unary family lifts to its native coefficient family. -/
theorem gamma_native_coefficient_preparation_exists (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (F : SelectedVFVolumeFamily C 1 a k)
    (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
    (σ : Fin (p+1) → Fin d) (ε : Fin d)
    (hR : ∀ t : Fin (p+1) → RV (M := M),
      {r : Fin d → RV (M := M) | (Fin.elim0,r) ∈ carrier R ∧ r ∘ σ=t}.Finite)
    (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero) (δ : Fin a)
    (hF : ∀ q : F.domain, F.form.value q=q.val.2 δ)
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
    (T : SpecialBijection (nativeMixedVolumeDomain hc F.domain) B) (hT : GammaChainDefinable G T.chain)
    (hB : SpecialTransformations.Section5.IsRVPullback (carrier B))
    (hJ : (nativeCoordinateCoefficientFamily hc C F R σ ε hR hε).Gamma G) :
    Nonempty (RVLabelConstraintSpecialPreparation T
      (nativeMixedVolumeDomain hc (nativeCoordinateCoefficientFamily hc C F R σ ε hR hε).densityGraph.domain)
      (independentRVDensityConstraint hc C Ξ hNames R δ ε) (Fin.castAdd 1 ∘ Fin.castAdd d) G) := by
  have hH := hJ.native_domain hc
  rw [native_coordinate_coefficient_density_graph_source hc C F R σ ε hR hε Ξ hNames δ hF] at hH ⊢
  exact gamma_rv_label_constraint_special_preparation_exists T hT hB _ hH _ _
    (constrained_unary_source_mem C Ξ hNames _ _ _)

/-- The prepared-head chart of a unary special preparation is Gamma-definable. -/
theorem unary_prepared_head_volume_iso_gamma (Ξ : Set (Values.Gamma (M := M)))
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a}
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
    (T : SpecialBijection A B) (hB : SpecialTransformations.Section5.IsRVPullback (carrier B))
    (hT : GammaChainDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.chain)
    (ρ : Fin (k+1) → Fin a) (δ : Fin a) (hδ : ∀ q ∈ carrier A, (q.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin 1 → SpecialTransformations.Section5.VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ=t}.Finite)
    (hSource : VolumeObjectGamma (standardAppendVolumeObject hc C Ξ A ρ δ hδ hfin
      (unarySpecialStandardContraction T hB)) G) :
    (unaryPreparedHeadVolumeIso hc C Ξ T hB hT ρ δ hδ hfin).GammaDefinable G :=
  gamma_volume_iso_of_label_identity hc _ hSource rfl (fun _ => rfl)

/-- The unary special standard contraction of a Gamma chain is a Gamma program. -/
theorem gamma_unary_special_standard_contraction
    {A : SpecialTransformations.Section5.DefSet (M := M) S 1 a}
    {B : SpecialTransformations.Section5.DefSet (M := M) S 1 b}
    (T : SpecialBijection A B) (hB : SpecialTransformations.Section5.IsRVPullback (carrier B))
    (hT : GammaChainDefinable G T.chain) :
    GammaProgramDefinable G (unarySpecialStandardContraction T hB).program :=
  gamma_standardFromProgram _ _ _ _ (gamma_unary_special_contraction_program T hB hT)

/-- Raw contraction labels of a Gamma set form a Gamma set. -/
theorem gamma_raw_contraction_labels_set
    (Q : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 l) (hQ : GammaSetDefinable G (carrier Q)) :
    GammaSetDefinable G {p : SpecialTransformations.Section5.Point (M := M) 0 l |
      p.2 ∈ (rawVolumeContractionLabels hc Q).carrier} := by
  have he : carrier Q = {p : SpecialTransformations.Section5.Point (M := M) 0 l |
      p.2 ∈ (rawVolumeContractionLabels hc Q).carrier} := by
    ext p
    have hp : p = (Fin.elim0,p.2) := Prod.ext (funext (fun i => Fin.elim0 i)) rfl
    change p ∈ carrier Q ↔ p.2 ∈ (rawVolumeContractionLabels hc Q).carrier
    rw [mem_rawVolumeContractionLabels hc Q p.2,← hp]
  exact he ▸ hQ

/-- Native product charts are Gamma-definable (they are coordinate selections). -/
theorem native_rv_product_volume_chart_iso_gamma
    (Q : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 l)
    (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d)
    (Z : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 r)
    (f : SpecialTransformations.Section5.Map Q (SpecialTransformations.Section5.PresentedSet.prod R Z))
    (hf : Function.Bijective f) (ι : Fin d → Fin l) (κ : Fin r → Fin l)
    (hι : ∀ q : Q, (f q).val.1.2=q.val.2 ∘ ι) (hκ : ∀ q : Q, (f q).val.2.2=q.val.2 ∘ κ)
    (σ : Fin (p+1) → Fin d) (τ : Fin (k+1) → Fin r) (δ : Fin d) (ε : Fin r)
    (hR : ∀ t : Fin (p+1) → RV (M := M), {s : Fin d → RV (M := M) | (Fin.elim0,s) ∈ carrier R ∧ s ∘ σ=t}.Finite)
    (hZ : ∀ t : Fin (k+1) → RV (M := M), {s : Fin r → RV (M := M) | (Fin.elim0,s) ∈ carrier Z ∧ s ∘ τ=t}.Finite)
    (hδ : ∀ q : R, (q.val.2 δ).val ≠ iRVZero) (hε : ∀ q : Z, (q.val.2 ε).val ≠ iRVZero)
    (hQ : GammaSetDefinable G (carrier Q)) :
    (nativeRVProductVolumeChartIso hc C Q R Z f hf ι κ hι hκ σ τ δ ε hR hZ hδ hε).GammaDefinable G := by
  have hD := gamma_raw_contraction_labels_set hc C Q hQ
  have hCoord : RVMapGamma (nativeRVProductVolumeChart hc C Q R Z f hf ι κ hι hκ σ τ δ ε hR hZ hδ hε).underlying.obj.volume G :=
    gamma_real_rv_map_graph hc G _ (rvCoordinateSelectMap G.real (Fin.append (m := p+1) (n := k+1) (ι ∘ σ) (κ ∘ τ))) hD (fun _ => rfl)
  refine gamma_real_rv_map_graph hc G _ (rvCoordinateSelectMap G.real (Fin.append ι κ))
    (gamma_essential_volume_domain _ hCoord) (fun u => ?_)
  change (nativeRVProductMapTransfer hc f ⟨u.val,SpecialTransformations.Section9.rvEssentialLabels_subset _ u.property⟩).val = u.val ∘ Fin.append ι κ
  rw [native_rv_product_map_transfer_value]
  simp only []
  rw [hι,hκ]
  funext j
  cases j using Fin.addCases <;> simp only [Function.comp_apply,Fin.append_left,Fin.append_right]


/-- The coefficient-times-prepared-head chart is Gamma-definable. -/
theorem coordinate_coefficient_contraction_product_iso_gamma (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (F : SelectedVFVolumeFamily C 1 a k')
    (R : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 d')
    (σ : Fin (p'+1) → Fin d') (ε : Fin d')
    (hR : ∀ t : Fin (p'+1) → RV (M := M),
      {r : Fin d' → RV (M := M) | (Fin.elim0,r) ∈ carrier R ∧ r ∘ σ=t}.Finite)
    (hε : ∀ q : R, (q.val.2 ε).val ≠ iRVZero) (δ : Fin a)
    (hδ : ∀ q ∈ F.domain.carrier, (q.2 δ).val ≠ iRVZero)
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b}
    (T : SpecialBijection (nativeMixedVolumeDomain hc F.domain) B)
    (hB : SpecialTransformations.Section5.IsRVPullback (carrier B))
    (hT : GammaChainDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.chain)
    (L : RVLabelConstraintSpecialPreparation T
      (nativeMixedVolumeDomain hc (nativeCoordinateCoefficientFamily hc C F R σ ε hR hε).densityGraph.domain)
      (independentRVDensityConstraint hc C Ξ hNames R δ ε) (Fin.castAdd 1 ∘ Fin.castAdd d')
      (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hSource : VolumeObjectGamma ((nativeCoordinateCoefficientFamily hc C F R σ ε hR hε).standardAppendObject hc Ξ
      (unarySpecialStandardContraction L.special L.pullback)) G)
    (hL : GammaSetDefinable G (carrier (headImage L.target))) :
    (coordinateCoefficientContractionProductIso hc C Ξ hNames F R σ ε hR hε δ hδ T hB hT L).GammaDefinable G := by
  unfold coordinateCoefficientContractionProductIso
  dsimp only
  refine RVVolumeIso.GammaDefinable.trans hc C G (gamma_volume_iso_of_label_identity hc _ hSource rfl (fun _ => rfl)) ?_
  exact native_rv_product_volume_chart_iso_gamma hc C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hL

end IntegrationInACVF.Section7
