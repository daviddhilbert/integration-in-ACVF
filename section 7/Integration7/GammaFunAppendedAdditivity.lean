import Integration7.GammaFunIntegralAdditivity

/-! Additivity of the appended-convention Gamma-named integral. Coordinate permutations and
degree reindexing descend to additive maps on Gamma classes; the appended integral object is the
permuted, reindexed canonical integral object, so appended additivity follows from canonical
additivity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section4 (rvCoprodLeftMap rvCoprodRightMap rvCoprod_value_left rvCoprod_value_right
  rvFiniteIsoOfAmbient rvReindexVolumeIso rvIsoOfVolumePreservingBijection)
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV)
open SpecialTransformations.DefinableGeometry (Map)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {n a k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

/-- Coordinate permutation of Gamma objects. -/
def GammaVolumeObjects.permuteVolume (U : GammaVolumeObjects B (C.base : Set M) k) (e : Equiv.Perm (Fin (k+1))) :
    GammaVolumeObjects B (C.base : Set M) k :=
  ⟨U.val.permuteVolume e,U.property.permuteVolume hc e⟩

/-- Coordinate permutation on Gamma classes. -/
def gammaClassPermute (e : Equiv.Perm (Fin (k+1))) :
    GammaVolumeBlowupClasses hc C B k → GammaVolumeBlowupClasses hc C B k :=
  Quotient.map (fun U => U.permuteVolume hc C e) (fun _ _ h => h.permuteVolume hc C e)

theorem gamma_class_permute_class (e : Equiv.Perm (Fin (k+1))) (U : GammaVolumeObjects B (C.base : Set M) k) :
    gammaClassPermute hc C e (gammaVolumeBlowupClass hc C B U) =
      gammaVolumeBlowupClass hc C B (U.permuteVolume hc C e) := rfl

theorem gamma_class_permute_add (e : Equiv.Perm (Fin (k+1))) (x y : GammaVolumeBlowupClasses hc C B k) :
    gammaClassPermute hc C e (x+y) = gammaClassPermute hc C e x + gammaClassPermute hc C e y := by
  induction x using Quotient.inductionOn with | h U => ?_
  induction y using Quotient.inductionOn with | h V => ?_
  change gammaVolumeBlowupClass hc C B ((U.coprod V).permuteVolume hc C e) =
    gammaVolumeBlowupClass hc C B ((U.permuteVolume hc C e).coprod (V.permuteVolume hc C e))
  let P := (U.val.coprod V.val).permuteVolume e
  let Q := (U.val.permuteVolume e).coprod (V.val.permuteVolume e)
  let f : Map P.underlying.obj.domain Q.underlying.obj.domain := Map.id _
  have hCoord : ∀ u, Q.underlying.obj.value (f u)=P.underlying.obj.value u := by
    intro u
    rcases volumeCoprod_cases U.val V.val u with ⟨r,rfl⟩ | ⟨r,rfl⟩
    · have hMap : f (rvCoprodLeftMap U.val.underlying.obj V.val.underlying.obj r)=
          rvCoprodLeftMap (U.val.permuteVolume e).underlying.obj (V.val.permuteVolume e).underlying.obj r :=
        Subtype.ext rfl
      change Q.underlying.obj.value (f (rvCoprodLeftMap U.val.underlying.obj V.val.underlying.obj r))=
        (U.val.coprod V.val).underlying.obj.value (rvCoprodLeftMap U.val.underlying.obj V.val.underlying.obj r) ∘ e
      have hNew := rvCoprod_value_left (U.val.permuteVolume e).underlying.obj (V.val.permuteVolume e).underlying.obj r
      have hOld := rvCoprod_value_left U.val.underlying.obj V.val.underlying.obj r
      exact (congrArg Q.underlying.obj.value hMap).trans (hNew.trans (congrArg (fun t => t ∘ e) hOld.symm))
    · have hMap : f (rvCoprodRightMap U.val.underlying.obj V.val.underlying.obj r)=
          rvCoprodRightMap (U.val.permuteVolume e).underlying.obj (V.val.permuteVolume e).underlying.obj r :=
        Subtype.ext rfl
      change Q.underlying.obj.value (f (rvCoprodRightMap U.val.underlying.obj V.val.underlying.obj r))=
        (U.val.coprod V.val).underlying.obj.value (rvCoprodRightMap U.val.underlying.obj V.val.underlying.obj r) ∘ e
      have hNew := rvCoprod_value_right (U.val.permuteVolume e).underlying.obj (V.val.permuteVolume e).underlying.obj r
      have hOld := rvCoprod_value_right U.val.underlying.obj V.val.underlying.obj r
      exact (congrArg Q.underlying.obj.value hMap).trans (hNew.trans (congrArg (fun t => t ∘ e) hOld.symm))
  have hS := ((U.coprod V).permuteVolume hc C e).property
  refine gammaVolumeBlowupClass_iso hc C B (RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f Function.bijective_id hCoord)) hCoord (fun _ => rfl)) ?_
  exact gamma_volume_iso_of_full_map _ f (gamma_essential_volume_domain _ hS.coordinates)
    (gamma_rv_coordinate_map hc _ id hS.domain_graph (fun _ => rfl)) (fun _ => rfl)

/-- Degree reindexing on Gamma classes. -/
def gammaClassReindex {p q : ℕ} (h : p = q) :
    GammaVolumeBlowupClasses hc C B q → GammaVolumeBlowupClasses hc C B p :=
  Quotient.map (fun U => U.reindexDegree h) (fun _ _ g => g.reindexDegree hc C h)

theorem gamma_class_reindex_class {p q : ℕ} (h : p = q) (U : GammaVolumeObjects B (C.base : Set M) q) :
    gammaClassReindex hc C h (gammaVolumeBlowupClass hc C B U) = gammaVolumeBlowupClass hc C B (U.reindexDegree h) :=
  rfl

theorem gamma_class_reindex_add {p q : ℕ} (h : p = q) (x y : GammaVolumeBlowupClasses hc C B q) :
    gammaClassReindex hc C h (x+y) = gammaClassReindex hc C h x + gammaClassReindex hc C h y := by
  subst h
  induction x using Quotient.inductionOn with | h U => ?_
  induction y using Quotient.inductionOn with | h V => ?_
  change gammaVolumeBlowupClass hc C B ((U.coprod V).reindexDegree rfl) =
    gammaVolumeBlowupClass hc C B (U.reindexDegree rfl) + gammaVolumeBlowupClass hc C B (V.reindexDegree rfl)
  rw [eq_of_heq (gamma_class_reindex_heq hc C B rfl (U.coprod V)),
    eq_of_heq (gamma_class_reindex_heq hc C B rfl U),
    eq_of_heq (gamma_class_reindex_heq hc C B rfl V)]
  rfl

set_option maxHeartbeats 2400000 in
/-- The appended object is the permuted, reindexed canonical object. -/
theorem gamma_selected_appended_permuted (G : Base (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (ρ : Fin (k+1) → Fin a) (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hfinA : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (T : StandardContraction A (Equiv.refl _)) (hT : GammaProgramDefinable G T.program) :
    GammaVolumeBlowupEquivalent G (C.base : Set M) (appendVolumeDegree (n+1) k)
      ((GammaVolumeObjects.reindexDegree ⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfinA T,
        GammaNamed.selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfinA T hT⟩
          (selected_append_degree_eq n k)).permuteVolume hc C (appendedToOriginalVolumePermutation (n+1) k).symm)
      ⟨standardAppendVolumeObject hc C G.gamma A ρ δ hδ hfinA T,
        standard_append_volume_object_gamma_of hc C G.gamma G A ρ δ hδ hfinA T hT⟩ := by
  let e := (appendedToOriginalVolumePermutation (n+1) k).symm
  let U : GammaVolumeObjects G (C.base : Set M) (appendVolumeDegree (n+1) k) :=
    GammaVolumeObjects.reindexDegree ⟨selectedStandardVolumeObject hc C G.gamma A ρ δ hδ hfinA T,
      GammaNamed.selected_standard_volume_object_gamma hc C G.gamma G A ρ δ hδ hfinA T hT⟩
        (selected_append_degree_eq n k)
  let fA := selectedIntegralCoordinateChart hc C G.gamma A ρ δ hδ hfinA T
  let fU : U.val.underlying ≅ (U.val.permuteVolume e).underlying :=
    rvFiniteIsoOfAmbient (rvReindexVolumeIso U.val.underlying.obj e)
  have hFU : RVMapGamma (finiteIsoMap fU) G :=
    gamma_real_rv_map_graph hc G _ (rvCoordinateSelectMap G.real id) U.property.coordinates.domain (fun _ => rfl)
  have hdA := selected_integral_coordinate_chart_density hc C G.gamma A ρ δ hδ hfinA T
  exact (GammaVolumeBlowupEquivalent.refl hc C G U).of_permuted_coordinate_charts hc C
    (V' := ⟨standardAppendVolumeObject hc C G.gamma A ρ δ hδ hfinA T,
      standard_append_volume_object_gamma_of hc C G.gamma G A ρ δ hδ hfinA T hT⟩)
    e fU fA.symm hFU
    (gamma_rv_coordinate_map hc _ id U.property.domain_graph (fun x => by
      have h1 : (finiteIsoMap fA (finiteIsoMap fA.symm x)).val = (finiteIsoMap fA.symm x).val ∘ id := rfl
      rw [finiteIsoMap_apply_symm] at h1
      exact h1.symm))
    (fun _ => rfl)
    (finite_volume_coordinate_chart_inverse fA _
      (selected_integral_coordinate_chart_coordinates hc C G.gamma A ρ δ hδ hfinA T))
    (fun _ => rfl)
    (fun v => by
      have h1 := hdA (finiteIsoMap fA.symm v)
      rw [finiteIsoMap_apply_symm] at h1
      exact h1.symm)

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ

/-- The appended integral is the permuted, reindexed canonical integral. -/
theorem presentation_appended_integral_eq_permute (F : Presentation C Ξ hΞ n k) :
    F.appendedIntegral hc C Ξ hΞ hGenerated =
      gammaClassPermute hc 𝔇 (appendedToOriginalVolumePermutation (n+1) k).symm
        (gammaClassReindex hc 𝔇 (selected_append_degree_eq n k) (F.integral hc C Ξ hΞ hGenerated)) :=
  ((gammaVolumeBlowupClass_eq_iff hc 𝔇 𝔅).mpr (gamma_selected_appended_permuted hc 𝔇 𝔅 _ _ _ _ _
    (F.contraction hc C Ξ hΞ hGenerated) (F.contraction_gamma hc C Ξ hΞ hGenerated))).symm

variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

include hγ hγ1 in
/-- **Additivity of the appended Gamma-named integral.** -/
theorem presentation_appended_integral_add (F H : Presentation C Ξ hΞ n k) :
    (F.add C Ξ hΞ H).appendedIntegral hc C Ξ hΞ hGenerated =
      F.appendedIntegral hc C Ξ hΞ hGenerated + H.appendedIntegral hc C Ξ hΞ hGenerated := by
  rw [presentation_appended_integral_eq_permute,presentation_appended_integral_eq_permute,
    presentation_appended_integral_eq_permute,presentation_integral_add hc C Ξ hΞ hGenerated γ hγ hγ1,
    gamma_class_reindex_add,gamma_class_permute_add]

end IntegrationInACVF.Section7.GammaFun
