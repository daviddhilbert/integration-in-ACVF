import Integration7.GammaFunPositiveIntegrals

/-! Gamma-named positive almost-everywhere functions and their integrals.
Removing the part of a presentation over a Gamma VF-small set does not change
its integral; this uses the coordinate VF realizations, their Gamma cofull
isomorphism and contraction invariance. Presentations whose rows have equal
Gamma-named classes outside a Gamma VF-small set are identified, and the
integral descends to the quotient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

/-- A Gamma VF set in `VF^(n+1)` coded over the named code context. -/
structure GammaVFSet (n : ℕ) where
  set : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawVFSpace (M := M) (n+1))
    ((gammaNamedCodeContext C Ξ hΞ).base : Set M)
  gamma : GammaSetDefinable (gammaNamedBase C Ξ) {p : Point (M := M) (n+1) 0 | p.1 ∈ set.carrier}

/-- The part of a presentation outside a Gamma VF set. -/
def Presentation.outsideBase (F : Presentation C Ξ hΞ n k) (E : GammaVFSet C Ξ hΞ n) : Presentation C Ξ hΞ n k :=
  ⟨F.arity,F.family.outsideBase E.set,F.gamma.outsideBase E.set E.gamma⟩

/-- The part of a presentation over a Gamma VF set. -/
def Presentation.overBase (F : Presentation C Ξ hΞ n k) (E : GammaVFSet C Ξ hΞ n) : Presentation C Ξ hΞ n k :=
  ⟨F.arity,F.family.restrict _ (definableMapPreimage_subset _ E.set),
    F.gamma.restrict _ _ (F.gamma.preimage E.set E.gamma)⟩

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem realization_gamma {m d c : ℕ} (A : SpecialTransformations.Section5.DefSet (M := M) 𝔖 (m+1) c)
    (hA : GammaSetDefinable 𝔅 (carrier A)) (ρ : Fin d → Fin c)
    (hfin : ∀ (x : Fin (m+1) → SpecialTransformations.Section5.VF (M := M))
      (t : Fin d → SpecialTransformations.Section5.RV (M := M)),
      {r : Fin c → SpecialTransformations.Section5.RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (δ : Fin c) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero) :
    VFVolumeObjectGamma (selectedCoordinateVolumeRealization hc A ρ hfin δ hδ) 𝔅 :=
  VFVolumeObjectGamma.of_density_graph (gamma_coordinate_volume_density_graph hc
    (gamma_native_program_selected_rv_vf_tail_lift hc A ρ hA) _ δ (fun _ => rfl))

set_option maxHeartbeats 2400000 in
include hγ hγ1 in
/-- **Small base removal.** -/
theorem presentation_integral_outside_base (F : Presentation C Ξ hΞ n k) (E : GammaVFSet C Ξ hΞ n)
    (hE : SpecialTransformations.Section4.vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1) E.set < n+1) :
    F.integral hc C Ξ hΞ hGenerated = (F.outsideBase C Ξ hΞ E).integral hc C Ξ hΞ hGenerated := by
  let F' := F.outsideBase C Ξ hΞ E
  let FE := F.overBase C Ξ hΞ E
  let A := nativeMixedVolumeDomain hc F.family.densityGraph.domain
  let A' := nativeMixedVolumeDomain hc F'.family.densityGraph.domain
  let D := nativeMixedVolumeDomain hc FE.family.densityGraph.domain
  have hA : GammaSetDefinable 𝔅 (carrier A) := F.gamma.native_domain hc
  have hA' : GammaSetDefinable 𝔅 (carrier A') := F'.gamma.native_domain hc
  let P := SpecialTransformations.DefinableGeometry.Map.fst (SpecialTransformations.Section4.rawVFSpace (M := M) (n+1))
    (SpecialTransformations.Section4.rawRVSpace F.arity) 𝔖 F.family.domain
  have hsub : carrier A' ⊆ carrier A := fun p hp =>
    ((mem_volumeDensityGraph_restrict F.family _ _ p).mp hp).1
  have hD : ∀ p ∈ carrier A, p ∉ carrier A' → p ∈ carrier D := by
    intro p hp hp'
    have hdom : (p.1,p.2 ∘ Fin.castAdd 1) ∈ F.family.domain.carrier :=
      ((mem_volumeDensityGraph_iff F.family.form p).mp hp).1
    apply (mem_volumeDensityGraph_restrict F.family _ _ p).mpr
    refine ⟨hp,?_⟩
    by_contra hnot
    exact hp' ((mem_volumeDensityGraph_restrict F.family _ _ p).mpr ⟨hp,hdom,hnot⟩)
  have hSmall : SpecialTransformations.Section4.vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1)
      (rawSpecialSet hc D) < n+1 := by
    rw [rawSpecialSet_nativeMixedVolumeDomain]
    refine (mixed_domain_vf_dim_le_base _ E.set ?_).trans_lt hE
    intro q
    have h := ((mem_volumeDensityGraph_iff FE.family.form q.val).mp q.property).1
    obtain ⟨b,hb,hbE⟩ := h
    change q.val.1 ∈ E.set.carrier
    change b.val.1 ∈ E.set.carrier at hbE
    rw [hb] at hbE
    exact hbE
  let ρ := F.family.densityGraph.selected
  have hW := realization_gamma hc C Ξ hΞ A hA ρ F.family.densityGraph.finite_selected (Fin.last F.arity)
    F.family.densityGraph_label_nonzero
  have hW' := realization_gamma hc C Ξ hΞ A' hA' ρ F'.family.densityGraph.finite_selected (Fin.last F.arity)
    F'.family.densityGraph_label_nonzero
  obtain ⟨f,hf⟩ := GammaNamed.gamma_selected_realization_cofull_iso hc 𝔇 𝔅 A A' D hsub hD ρ
    F.family.densityGraph.finite_selected F'.family.densityGraph.finite_selected FE.family.densityGraph.finite_selected
    (Fin.last F.arity) F.family.densityGraph_label_nonzero F'.family.densityGraph_label_nonzero
    FE.family.densityGraph_label_nonzero hSmall hW'
  have hBC := gamma_named_code_context_base C Ξ hΞ
  have hreal := (Cardinal.mk_le_mk_of_subset hBC).trans_lt (𝔇).small
  let W := selectedCoordinateVolumeRealization hc A ρ F.family.densityGraph.finite_selected (Fin.last F.arity)
    F.family.densityGraph_label_nonzero
  let W' := selectedCoordinateVolumeRealization hc A' ρ F'.family.densityGraph.finite_selected (Fin.last F.arity)
    F'.family.densityGraph_label_nonzero
  obtain ⟨EW,hEW,_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc W.densityGraph.domain) hW.densityGraph (Equiv.refl _)
  obtain ⟨EW',hEW',_,_,_⟩ := generated_base_standard_contraction_exists (B := 𝔅) (𝔇).saturated (𝔇).model00
    hreal hGenerated hBC (nativeMixedVolumeDomain hc W'.densityGraph.domain) hW'.densityGraph (Equiv.refl _)
  have hNames := gamma_named_code_context_names C Ξ hΞ
  have hGeneric : ∀ {p : ℕ} (x : Fin p → SpecialTransformations.Section5.VF (M := M)),
      AlgebraicIndependent (vfParameterField (𝔅).real) x → AlgebraicIndependent (vfParameterField 𝔖) x :=
    fun x hx => gamma_named_code_context_generic C Ξ hΞ hc x hx
  have h1 := GammaNamed.gamma_selected_realization_contraction hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    A hA ρ F.family.densityGraph.finite_selected (Fin.last F.arity) F.family.densityGraph_label_nonzero
    (F.contraction hc C Ξ hΞ hGenerated) (F.contraction_gamma hc C Ξ hΞ hGenerated) hW EW hEW
  have h2 := GammaNamed.gamma_selected_realization_contraction hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    A' hA' ρ F'.family.densityGraph.finite_selected (Fin.last F.arity) F'.family.densityGraph_label_nonzero
    (F'.contraction hc C Ξ hΞ hGenerated) (F'.contraction_gamma hc C Ξ hΞ hGenerated) hW' EW' hEW'
  have h3 := GammaNamed.gamma_vf_iso_contraction_comparison hc 𝔇 𝔅 hBC hΞ hGenerated hNames hGeneric γ hγ hγ1
    _ _ hW' hW f hf EW' EW hEW' hEW
  exact (gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr
    (((h1.trans hc (h3.symm hc)).trans hc (h2.symm hc)).descend hc 𝔇 hNames)

end IntegrationInACVF.Section7.GammaFun
