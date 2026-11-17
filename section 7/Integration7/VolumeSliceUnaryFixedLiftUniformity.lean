module

public import Integration7.GammaUnaryFixedLiftCommonSchema
public import Integration7.GammaLabelDensityCoordinateRows
public import Integration7.VolumeSliceCommonUniformity
public import IntegrationSection6.GammaRVParameterFieldBase

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! VF-fixed, density-preserving comparisons of all unary RV-prefix
slices glue to common forward volume blowups of the original objects. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {e : ℕ}

set_option maxHeartbeats 1600000 in
theorem gamma_volume_slice_unary_fixed_lift_uniformity {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ) (FBase : VFFieldBase B.real)
    (C : BaseContext M) (U V : GammaRVFiniteObject B (e+1))
    (hUC : U.codes ⊆ (C.base : Set M)) (hVC : V.codes ⊆ (C.base : Set M))
    (δ : Fin (rvObjectArity U.object)) (ε : Fin (rvObjectArity V.object))
    (hδ : ∀ u : rvObjectDomain U.object, (u.val δ).val ≠ iRVZero)
    (hε : ∀ v : rvObjectDomain V.object, (v.val ε).val ≠ iRVZero)
    (hLift : ∀ t : Fin e → RV (M := M),
      ∀ P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (rvValues t),B.gamma⟩
        (rvObjectArity U.object) 1 ((gammaVolumeSliceSchema U).rowDomain (rvValues t))
        ((gammaVolumeSliceSchema U).rowVolume (rvValues t)),
      ∀ Q : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (rvValues t),B.gamma⟩
        (rvObjectArity V.object) 1 ((gammaVolumeSliceSchema V).rowDomain (rvValues t))
        ((gammaVolumeSliceSchema V).rowVolume (rvValues t)),
      ∃ f : GammaIso ⟨B.real ∪ Set.range (rvValues t),B.gamma⟩ P.toGamma.lift Q.toGamma.lift,
        (∀ u, (f.equiv u).val.1 = u.val.1) ∧
        (∀ u, (f.equiv u).val.2 ε = u.val.2 δ)) :
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
      VolumeBlowupEquivalent
        ((gammaCoordinateDensityObject (e := e) (k := 0) hc C U hUC δ hδ).extend hCD)
        ((gammaCoordinateDensityObject (e := e) (k := 0) hc C V hVC ε hε).extend hCD) := by
  obtain ⟨NF,hNF⟩ := gammaVolumeSliceDensitySchema_uniform_bound hκ hs hreal hgamma U δ hδ
  obtain ⟨NG,hNG⟩ := gammaVolumeSliceDensitySchema_uniform_bound hκ hs hreal hgamma V ε hε
  apply gamma_volume_slice_density_common_uniformity hc hκ hs hreal hgamma C U V hUC hVC δ ε hδ hε NF NG
  intro t
  let F := (gammaVolumeSliceDensitySchema U δ).withBound NF
  let G := (gammaVolumeSliceDensitySchema V ε).withBound NG
  obtain ⟨P⟩ := F.realize (rvValues t) (hNF t)
  obtain ⟨Q⟩ := G.realize (rvValues t) (hNG t)
  have hPδ : ∀ u : P.finite.domain, (u.val δ).val ≠ iRVZero := by
    intro u
    have hx : u.val ∈ (gammaVolumeSliceSchema U).rowDomain (rvValues t) := P.finite.domain_eq.le u.property
    obtain ⟨v,hv,_⟩ := (gammaVolumeSliceSchema_domain U t u.val).mp hx
    exact fun hz => hδ v ((congrArg (fun r => (r δ).val) hv).trans hz)
  have hQε : ∀ u : Q.finite.domain, (u.val ε).val ≠ iRVZero := by
    intro u
    have hx : u.val ∈ (gammaVolumeSliceSchema V).rowDomain (rvValues t) := Q.finite.domain_eq.le u.property
    obtain ⟨v,hv,_⟩ := (gammaVolumeSliceSchema_domain V t u.val).mp hx
    exact fun hz => hε v ((congrArg (fun r => (r ε).val) hv).trans hz)
  let Ct := finiteVolumeParameterContext C (Set.range (rvValues t)) (Set.finite_range _)
  have hB : B.real ∪ Set.range (rvValues t) ⊆ (Ct.base : Set M) := by
    intro x hx
    rcases hx with hx | hx
    · exact finiteVolumeParameterContext_contains C _ (Set.finite_range _)
        (Or.inl (hUC (U.real_contains hx)))
    · exact finiteVolumeParameterContext_contains C _ (Set.finite_range _) (Or.inr hx)
  obtain ⟨C₁,hCtC₁,hP⟩ := P.exists_containingContext Ct hB
  obtain ⟨C₂,hC₁C₂,hQ⟩ := Q.exists_containingContext C₁ (hB.trans hCtC₁)
  have hP₂ := hP.trans hC₁C₂
  have PL := gamma_label_density_coordinate_row hc C₂ F (rvValues t) (hNF t) P hP₂ δ
    (gammaVolumeSliceDensitySchema_row U δ hδ t) hPδ
  have PR := gamma_label_density_coordinate_row hc C₂ G (rvValues t) (hNG t) Q hQ ε
    (gammaVolumeSliceDensitySchema_row V ε hε t) hQε
  obtain ⟨f,hVF,hLabel⟩ := hLift t P.finite Q.finite
  exact gamma_unary_fixed_lift_common_schema (sp := fun _ => .rv) hc C₂ hκ hs hreal hgamma (rvValues t)
    (fun j => (t j).property) γ hγ hγ1
    (VFFieldBase.withRVParameters FBase (rvValues t) (fun j => (t j).property))
    P.finite.toGamma Q.finite.toGamma hP₂ hQ δ ε hPδ hQε f hVF hLabel F G (hNF t) (hNG t) PL PR

end IntegrationInACVF.Section7
