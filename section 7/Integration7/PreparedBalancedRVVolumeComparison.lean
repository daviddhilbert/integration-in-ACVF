import Integration7.PreparedUnaryRVValueProducts
import Integration7.BalancedUnaryRVVolumeIsomorphisms
import Integration7.GammaCoordinateDensityGraphs
import Integration7.GradedVolumeProducts

/-! Actual original-Gamma volume isomorphisms between the two balanced
product RV objects, constructed from the chosen unary preparations.
Their nonzero unary labels are retained as actual essential domains. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.Cells

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {m l u v : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

set_option maxHeartbeats 2400000 in
theorem prepared_balanced_rv_volume_comparison {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (P : Base (M := M)) (hsmall : Cardinal.mk P.real < κ) (hPS : P.real ⊆ S)
    (hcM : CanonicalStructure.IsCanonical (M := M))
    {R : Set (VF (M := M) × VF (M := M))} {ε : VF (M := M) → VF (M := M)}
    {r t : RV (M := M)} (h : IsBalanced R ε r t) (hr : r ≠ rv (0 : VF (M := M)))
    (hrS : r.val ∈ S) (htS : t.val ∈ S) (hr0 : r.val ≠ iRVZero) (ht0 : t.val ≠ iRVZero)
    {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
    {A' : DefSet (M := M) S 1 u} {B' : DefSet (M := M) S 1 v}
    (f : Map A B) (hf : Function.Bijective f)
    (hDomain : ∀ p : A, vfAt p.val 0 ∈ first R)
    (hValue : ∀ p : A, vfAt (f p).val 0 = ε (vfAt p.val 0))
    (TA : SpecialBijection A A') (TB : SpecialBijection B B')
    (hA' : IsRVPullback (carrier A')) (hB' : IsRVPullback (carrier B'))
    (hAΓ : GammaSetDefinable P (carrier A')) (hBΓ : GammaSetDefinable P (carrier B'))
    (hc : Contractible (unaryConjugate TA TB f))
    (hback : Contractible (Map.inverse (unaryConjugate TA TB f) (unaryConjugate_bijective TA TB f hf)))
    (hgΓ : GammaGraphDefinable P (pointMapGraph (unaryConjugate TA TB f)))
    (hAF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M N _ _ S _ _
      (rvObjectVolume (pullbackObject A')))
    (hBF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M N _ _ S _ _
      (rvObjectVolume (pullbackObject B'))) :
    let U₀ := canonicalFiniteRVObject hcM ⟨pullbackObject A',hAF⟩
    let V₀ := canonicalFiniteRVObject hcM ⟨pullbackObject B',hBF⟩
    let U := rvFiniteEssential U₀
    let V := rvFiniteEssential V₀
    ∃ i : RVVolumeIso (prependFixedRVVolume V r hrS (VolumeForm.one V.obj.domain))
        (appendFixedRVVolume U t htS (VolumeForm.one U.obj.domain)), i.GammaDefinable P := by
  intro U₀ V₀ U V
  let g := unaryConjugate TA TB f
  have hg := unaryConjugate_bijective TA TB f hf
  let e : U₀ ≅ V₀ := rvFiniteIsoOfAmbient (canonicalRVIso hcM
    (unaryRVIso hκ hs hsmall g hg hc hback hA' hB' hgΓ))
  let F := finiteIsoMap (rvFiniteEssentialIso e).symm
  have hF := finiteIsoMap_bijective (rvFiniteEssentialIso e).symm
  have hU (z : U.obj.domain) : (U.obj.value z 0).val ≠ iRVZero :=
    rvEssential_value_nonzero U₀.obj z 0
  have hV (z : V.obj.domain) : (V.obj.value z 0).val ≠ iRVZero :=
    rvEssential_value_nonzero V₀.obj z 0
  have hProducts := prepared_unary_rv_value_products hκ hs P hsmall hcM h hr f hf hDomain hValue
    TA TB hA' hB' hc hback hgΓ hAF hBF
  have hProduct (z : V.obj.domain) : Values.vrv r*Values.vrv (V.obj.value z 0) =
      Values.vrv (U.obj.value (F z) 0)*Values.vrv t := by
    let z₀ : V₀.obj.domain := ⟨z.val,rvEssentialLabels_subset V₀.obj z.property⟩
    let x₀ : U₀.obj.domain := ⟨(F z).val,rvEssentialLabels_subset U₀.obj (F z).property⟩
    have he : finiteIsoMap e x₀ = z₀ := finiteIsoMap_apply_symm e z₀
    have hp := hProducts x₀ (hU (F z))
    change Values.vrv r*Values.vrv (V₀.obj.value z₀ 0) = Values.vrv (U₀.obj.value x₀ 0)*Values.vrv t
    exact (congrArg (fun y : V₀.obj.domain => Values.vrv r*Values.vrv (V₀.obj.value y 0)) he).symm.trans hp
  have hVΓ : GammaSetDefinable P {p : Point (M := M) 0 V.obj.arity | p.2 ∈ V.obj.domain.carrier} :=
    gamma_essential_volume_domain (⟨V₀,VolumeForm.one V₀.obj.domain⟩ : PositiveRVVolumeObject (M := M) S 0)
      (canonical_gamma_object_volume_graph hcM (FiniteRV.gammaPullbackAt hPS B' hBΓ hBF))
  have hFullΓ : GammaGraphDefinable P
      (fun (p : Point (M := M) 0 V₀.obj.arity) (q : Point (M := M) 0 U₀.obj.arity) =>
        ∃ z : V₀.obj.domain, z.val = p.2 ∧ (finiteIsoMap e.symm z).val = q.2) := by
    apply GammaGraphDefinable.congr (gamma_rvContractionMap_graph (Map.inverse g hg) hback
      (gamma_inverse_map_graph g hg hgΓ))
    intro p q
    constructor
    · rintro ⟨z,hz,hq⟩
      exact ⟨⟨z.val,z.property⟩,hz,hq⟩
    · rintro ⟨z,hz,hq⟩
      exact ⟨⟨z.val,z.property⟩,hz,hq⟩
  have hGraph : GammaGraphDefinable P
      (fun (p : Point (M := M) 0 V.obj.arity) (q : Point (M := M) 0 U.obj.arity) =>
        ∃ z : V.obj.domain, z.val = p.2 ∧ (F z).val = q.2) := by
    apply GammaGraphDefinable.congr ((gammaLogicInput P).restrict_graph hVΓ hFullΓ)
    intro p q
    constructor
    · rintro ⟨hp,z,hz,hq⟩
      exact ⟨⟨z.val,hz.symm ▸ hp⟩,hz,hq⟩
    · rintro ⟨z,hz,hq⟩
      refine ⟨?_,⟨z.val,rvEssentialLabels_subset V₀.obj z.property⟩,hz,hq⟩
      change p.2 ∈ V.obj.domain.carrier
      exact hz ▸ z.property
  refine ⟨balancedUnaryRVVolumeIso U V r t hrS htS hr0 ht0 hU hV F hF
    (VolumeForm.one U.obj.domain) (VolumeForm.one V.obj.domain) (fun _ => rfl) hProduct,?_⟩
  exact balanced_unary_rv_volume_iso_gamma U V r t hrS htS hr0 ht0 hU hV F hF
    (VolumeForm.one U.obj.domain) (VolumeForm.one V.obj.domain) (fun _ => rfl) hProduct hVΓ hGraph

end IntegrationInACVF.Section7
