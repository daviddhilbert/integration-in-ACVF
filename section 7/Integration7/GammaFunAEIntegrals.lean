import Integration7.GammaFunPositiveIntegrals
import Integration7.AERVVolumeFunctionIntegrals

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


/-! ### The almost-everywhere quotient -/

/-- The Gamma-named class of the row of a presentation at a VF point. -/
def Presentation.rowClass (F : Presentation C Ξ hΞ n k) (x : Fin (n+1) → VFType (M := M)) :
    GammaVolumeBlowupClasses hc (vfParameterVolumeContext 𝔇 x) (rowGammaBase 𝔅 x) k :=
  gammaVolumeBlowupClass hc (vfParameterVolumeContext 𝔇 x) (rowGammaBase 𝔅 x)
    ⟨F.family.rowInContext x,F.gamma.row hc x⟩

/-- The empty Gamma VF set. -/
def GammaVFSet.empty (n : ℕ) : GammaVFSet C Ξ hΞ n :=
  ⟨SpecialTransformations.DefinableGeometry.DefSet.empty _ _,by
    have h := gamma_empty_point_set (G := 𝔅) (n := n+1) (a := 0)
    convert h using 1
    exact Set.eq_empty_iff_forall_notMem.mpr (fun p hp => hp)⟩

/-- The union of Gamma VF sets. -/
def GammaVFSet.union (E D : GammaVFSet C Ξ hΞ n) : GammaVFSet C Ξ hΞ n :=
  ⟨E.set.union D.set,by
    have h := (gammaLogicInput 𝔅).union E.gamma D.gamma
    convert h using 1
    ext p
    exact Iff.rfl⟩

/-- Almost-everywhere equivalence of Gamma-named presentations. -/
def AEEquivalent (F H : Presentation C Ξ hΞ n k) : Prop :=
  ∃ E : GammaVFSet C Ξ hΞ n,
    SpecialTransformations.Section4.vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1) E.set < n+1 ∧
      ∀ x, x ∉ E.set.carrier → F.rowClass hc C Ξ hΞ x = H.rowClass hc C Ξ hΞ x

def aeSetoid (n k : ℕ) : Setoid (Presentation C Ξ hΞ n k) where
  r := AEEquivalent hc C Ξ hΞ
  iseqv := ⟨fun _ => ⟨GammaVFSet.empty C Ξ hΞ n,(SpecialTransformations.DefinableGeometry.Dimension.dim_empty SpecialTransformations.Section4.rawVFSpace
      (SpecialTransformations.Section4.AuxiliaryCoordinates.space (SpecialTransformations.Section4.rawRVSpace (M := M) 1)) (SpecialTransformations.Section4.AuxiliaryCoordinates.rv 0)).trans_lt
        (Nat.zero_lt_succ n),fun _ _ => rfl⟩,
    fun ⟨E,hE,h⟩ => ⟨E,hE,fun x hx => (h x hx).symm⟩,
    fun ⟨E,hE,h⟩ ⟨D,hD,g⟩ => ⟨E.union C Ξ hΞ D,by
      change SpecialTransformations.Section4.vfDim _ (E.set.union D.set) < n+1
      rw [pure_vf_dim_union hc 𝔇]
      exact max_lt hE hD,
      fun x hx => (h x (fun he => hx (Or.inl he))).trans (g x (fun hd => hx (Or.inr hd)))⟩⟩

/-- **Gamma-named positive almost-everywhere functions** on `VF^(n+1)` with coefficient
degree `k+1`. -/
abbrev AEFunction (n k : ℕ) := Quotient (aeSetoid hc C Ξ hΞ n k)

theorem gamma_outside_base_row_iso (F : Presentation C Ξ hΞ n k) (E : GammaVFSet C Ξ hΞ n)
    (x : Fin (n+1) → VFType (M := M)) (hx : x ∉ E.set.carrier) :
    (selectedFamilyOutsideBaseRowIso hc F.family E.set x hx).GammaDefinable (rowGammaBase 𝔅 x) := by
  have hR := (F.outsideBase C Ξ hΞ E).gamma.row hc x
  exact gamma_volume_iso_of_preserving_coordinates_full hc (vfParameterVolumeContext 𝔇 x) _
    (fun _ => rfl) (fun _ => rfl) (gamma_essential_volume_domain _ hR.coordinates)
    ((gamma_rv_coordinate_map hc
      (SpecialTransformations.DefinableGeometry.Map.inclusion (fun r hr => hr.1) :
        SpecialTransformations.DefinableGeometry.Map ((F.outsideBase C Ξ hΞ E).family.rowInContext x).underlying.obj.domain
          (F.family.rowInContext x).underlying.obj.domain) id hR.domain_graph (fun _ => rfl)).congr (fun _ => rfl))

include hγ hγ1 in
/-- The integral descends to almost-everywhere functions. -/
theorem presentation_integral_ae (F H : Presentation C Ξ hΞ n k) (h : AEEquivalent hc C Ξ hΞ F H) :
    F.integral hc C Ξ hΞ hGenerated = H.integral hc C Ξ hΞ hGenerated := by
  obtain ⟨E,hE,hRows⟩ := h
  refine (presentation_integral_outside_base hc C Ξ hΞ hGenerated γ hγ hγ1 F E hE).trans
    (((presentation_integral_eq_of_rows hc C Ξ hΞ hGenerated γ hγ hγ1 _ _ ?_)).trans
      (presentation_integral_outside_base hc C Ξ hΞ hGenerated γ hγ hγ1 H E hE).symm)
  intro x
  let Cx := vfParameterVolumeContext 𝔇 x
  by_cases hx : x ∈ E.set.carrier
  · have hF0 := selected_family_outside_base_row_empty F.family E.set x hx
    have hH0 := selected_family_outside_base_row_empty H.family E.set x hx
    refine GammaVolumeBlowupEquivalent.of_iso Cx (rowGammaBase 𝔅 x) (RVVolumeIso.of_empty hc Cx _ _ hF0 hH0) ?_
    apply GammaGraphDefinable.congr (FiniteRV.gamma_empty_graph (B := rowGammaBase 𝔅 x) _ _)
    intro p q
    constructor
    · exact False.elim
    · rintro ⟨u,_,_⟩
      exact (hF0.le (rvEssentialLabels_subset _ u.property)).elim
  · have h1 := GammaVolumeBlowupEquivalent.of_iso Cx (rowGammaBase 𝔅 x)
      (U := ⟨(F.outsideBase C Ξ hΞ E).family.rowInContext x,(F.outsideBase C Ξ hΞ E).gamma.row hc x⟩)
      (V := ⟨F.family.rowInContext x,F.gamma.row hc x⟩) _ (gamma_outside_base_row_iso hc C Ξ hΞ F E x hx)
    have h2 := GammaVolumeBlowupEquivalent.of_iso Cx (rowGammaBase 𝔅 x)
      (U := ⟨(H.outsideBase C Ξ hΞ E).family.rowInContext x,(H.outsideBase C Ξ hΞ E).gamma.row hc x⟩)
      (V := ⟨H.family.rowInContext x,H.gamma.row hc x⟩) _ (gamma_outside_base_row_iso hc C Ξ hΞ H E x hx)
    exact (h1.trans hc Cx _ ((gammaVolumeBlowupClass_eq_iff hc Cx _).mp (hRows x hx))).trans hc Cx _
      (h2.symm hc Cx _)

include hγ hγ1 in
/-- **The Gamma-named integral of an almost-everywhere function.** -/
def aeIntegral : AEFunction hc C Ξ hΞ n k → HK.GammaNamedRVClasses hc C Ξ hΞ (((k+1)+n)+1) :=
  Quotient.lift (fun F => F.integral hc C Ξ hΞ hGenerated)
    (fun F H h => presentation_integral_ae hc C Ξ hΞ hGenerated γ hγ hγ1 F H h)

end IntegrationInACVF.Section7.GammaFun
