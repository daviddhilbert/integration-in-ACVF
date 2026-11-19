import Integration7.GammaFunZeroAddition
import Integration7.RVLabelCutHeadPreparations
import Integration7.SelectedSumTagPredicates
import Integration7.CommonContextVolumePartitions
import Integration7.GammaActualVolumePartitions

/-! Rows of native coordinate families on Gamma sets. A coordinate selection that is a
bijection on rows and respects selected coordinates and densities identifies the rows up to
Gamma isomorphism; the rows of a native family are the coproduct of the rows of its two
complementary Gamma label cuts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {p m m' k : ℕ}

theorem rv_label_cut_fin {G : Base (M := M)} {S : Set M} {j : ℕ}
    (K : SpecialTransformations.Section5.DefSet (M := M) S p m) (hK : GammaSetDefinable G (carrier K))
    (ι : Fin j → Fin m) (R : Set (Point (M := M) 0 j)) (hR : GammaSetDefinable G R)
    (hNames : commonRealNames G ⊆ S) (ρ : Fin (k+1) → Fin m)
    (hfin : ∀ (x : Fin p → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier K ∧ r ∘ ρ = t}.Finite) :
    ∀ (x : Fin p → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier (rvLabelCut K hK ι R hR hNames) ∧ r ∘ ρ = t}.Finite :=
  fun y t => (hfin y t).subset (fun _ h => ⟨h.1.1,h.2⟩)

theorem rv_label_cut_density {G : Base (M := M)} {S : Set M} {j : ℕ}
    (K : SpecialTransformations.Section5.DefSet (M := M) S p m) (hK : GammaSetDefinable G (carrier K))
    (ι : Fin j → Fin m) (R : Set (Point (M := M) 0 j)) (hR : GammaSetDefinable G R)
    (hNames : commonRealNames G ⊆ S) (δ : Fin m) (hδ : ∀ q ∈ carrier K, (q.2 δ).val ≠ iRVZero) :
    ∀ q ∈ carrier (rvLabelCut K hK ι R hR hNames), (q.2 δ).val ≠ iRVZero :=
  fun q hq => hδ q hq.1

set_option maxHeartbeats 800000 in
/-- **Coordinate selections identify native rows.** -/
theorem native_row_select_equivalent (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M))
    (U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) p m)
    (V : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) p m')
    (hU : GammaSetDefinable G (carrier U)) (hV : GammaSetDefinable G (carrier V))
    (ρ : Fin (k+1) → Fin m) (τ : Fin (k+1) → Fin m')
    (hfinU : ∀ (x : Fin p → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (hfinV : ∀ (x : Fin p → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin m' → RV (M := M) | (x,r) ∈ carrier V ∧ r ∘ τ = t}.Finite)
    (δ : Fin m) (ε : Fin m') (hδ : ∀ q ∈ carrier U, (q.2 δ).val ≠ iRVZero)
    (hε : ∀ q ∈ carrier V, (q.2 ε).val ≠ iRVZero)
    (σ : Fin m' → Fin m)
    (hmap : ∀ (x : Fin p → VF (M := M)) (t : Fin m → RV (M := M)), (x,t) ∈ carrier U → (x,t ∘ σ) ∈ carrier V)
    (hsurj : ∀ (x : Fin p → VF (M := M)) (s : Fin m' → RV (M := M)), (x,s) ∈ carrier V →
      ∃ t, (x,t) ∈ carrier U ∧ t ∘ σ = s)
    (hinj : ∀ (x : Fin p → VF (M := M)) (t t' : Fin m → RV (M := M)), (x,t) ∈ carrier U → (x,t') ∈ carrier U →
      t ∘ σ = t' ∘ σ → t = t')
    (hsel : ∀ (x : Fin p → VF (M := M)) (t : Fin m → RV (M := M)), (x,t) ∈ carrier U → (t ∘ σ) ∘ τ = t ∘ ρ)
    (hden : ∀ (x : Fin p → VF (M := M)) (t : Fin m → RV (M := M)), (x,t) ∈ carrier U → t (σ ε) = t δ)
    (x : Fin p → VFType (M := M)) :
    GammaVolumeBlowupEquivalent (rowGammaBase G x) ((vfParameterVolumeContext C x).base : Set M) k
      ⟨(nativeCoordinateVolumeFamily hc U ρ hfinU δ hδ).rowInContext x,
        (native_coordinate_volume_family_gamma hc U hU ρ hfinU δ hδ).row hc x⟩
      ⟨(nativeCoordinateVolumeFamily hc V τ hfinV ε hε).rowInContext x,
        (native_coordinate_volume_family_gamma hc V hV τ hfinV ε hε).row hc x⟩ := by
  let N := nativeCoordinateVolumeFamily hc U ρ hfinU δ hδ
  let N' := nativeCoordinateVolumeFamily hc V τ hfinV ε hε
  let Cx := vfParameterVolumeContext C x
  let f : SpecialTransformations.DefinableGeometry.Map (N.rowInContext x).underlying.obj.domain
      (N'.rowInContext x).underlying.obj.domain :=
    ((rvCoordinateSelectMap (Cx.base : Set M) σ).comp
      (SpecialTransformations.DefinableGeometry.Map.inclusion (fun _ _ => Set.mem_univ _))).corestrict
      (fun s => hmap x s.val s.property)
  have hfv : ∀ s, (f s).val = s.val ∘ σ := fun _ => rfl
  have hf : Function.Bijective f := by
    constructor
    · intro s s' h
      apply Subtype.ext
      exact hinj x s.val s'.val s.property s'.property
        ((hfv s).symm.trans ((congrArg (fun w : (N'.rowInContext x).underlying.obj.domain => w.val) h).trans (hfv s')))
    · intro t
      obtain ⟨s,hs,hst⟩ := hsurj x t.val t.property
      exact ⟨⟨s,hs⟩,Subtype.ext hst⟩
  have hCoord : ∀ s, (N'.rowInContext x).underlying.obj.value (f s) = (N.rowInContext x).underlying.obj.value s := by
    intro s
    exact hsel x s.val s.property
  have hForm : ∀ s, (N'.rowInContext x).form.value (f s) = (N.rowInContext x).form.value s := by
    intro s
    exact hden x s.val s.property
  have hS := (native_coordinate_volume_family_gamma hc U hU ρ hfinU δ hδ).row hc x
  refine GammaVolumeBlowupEquivalent.of_iso Cx (rowGammaBase G x)
    (RVVolumeIso.of_preserving_coordinates_full hc Cx
      (SpecialTransformations.Section4.rvFiniteIsoOfAmbient
        (SpecialTransformations.Section4.rvIsoOfVolumePreservingBijection f hf hCoord)) hCoord hForm) ?_
  exact gamma_volume_iso_of_full_map _ f (gamma_essential_volume_domain _ hS.coordinates)
    (gamma_rv_coordinate_map hc _ σ hS.domain_graph (fun _ => rfl)) (fun _ => rfl)

set_option maxHeartbeats 800000 in
/-- **Native rows split along a Gamma label cut.** -/
theorem native_row_cut_class (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hNames : commonRealNames G ⊆ (C.base : Set M)) {j : ℕ}
    (K : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) p m)
    (hK : GammaSetDefinable G (carrier K)) (ρ : Fin (k+1) → Fin m)
    (hfin : ∀ (x : Fin p → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier K ∧ r ∘ ρ = t}.Finite)
    (δ : Fin m) (hδ : ∀ q ∈ carrier K, (q.2 δ).val ≠ iRVZero)
    (ι : Fin j → Fin m) (R : Set (Point (M := M) 0 j)) (hR : GammaSetDefinable G R)
    (hRc : GammaSetDefinable G (Set.univ \ R)) (x : Fin p → VFType (M := M)) :
    gammaVolumeBlowupClass hc (vfParameterVolumeContext C x) (rowGammaBase G x)
        ⟨(nativeCoordinateVolumeFamily hc K ρ hfin δ hδ).rowInContext x,
          (native_coordinate_volume_family_gamma hc K hK ρ hfin δ hδ).row hc x⟩ =
      gammaVolumeBlowupClass hc (vfParameterVolumeContext C x) (rowGammaBase G x)
          ⟨(nativeCoordinateVolumeFamily hc (rvLabelCut K hK ι R hR hNames) ρ
              (rv_label_cut_fin K hK ι R hR hNames ρ hfin) δ (rv_label_cut_density K hK ι R hR hNames δ hδ)).rowInContext x,
            (native_coordinate_volume_family_gamma hc _ (gamma_rv_label_cut K hK ι R hR) ρ
              (rv_label_cut_fin K hK ι R hR hNames ρ hfin) δ (rv_label_cut_density K hK ι R hR hNames δ hδ)).row hc x⟩ +
        gammaVolumeBlowupClass hc (vfParameterVolumeContext C x) (rowGammaBase G x)
          ⟨(nativeCoordinateVolumeFamily hc (rvLabelCut K hK ι (Set.univ \ R) hRc hNames) ρ
              (rv_label_cut_fin K hK ι (Set.univ \ R) hRc hNames ρ hfin) δ
              (rv_label_cut_density K hK ι (Set.univ \ R) hRc hNames δ hδ)).rowInContext x,
            (native_coordinate_volume_family_gamma hc _ (gamma_rv_label_cut K hK ι (Set.univ \ R) hRc) ρ
              (rv_label_cut_fin K hK ι (Set.univ \ R) hRc hNames ρ hfin) δ
              (rv_label_cut_density K hK ι (Set.univ \ R) hRc hNames δ hδ)).row hc x⟩ := by
  let Cx := vfParameterVolumeContext C x
  let Bx := rowGammaBase G x
  let N := nativeCoordinateVolumeFamily hc K ρ hfin δ hδ
  let NL := nativeCoordinateVolumeFamily hc (rvLabelCut K hK ι R hR hNames) ρ
    (rv_label_cut_fin K hK ι R hR hNames ρ hfin) δ (rv_label_cut_density K hK ι R hR hNames δ hδ)
  let NR := nativeCoordinateVolumeFamily hc (rvLabelCut K hK ι (Set.univ \ R) hRc hNames) ρ
    (rv_label_cut_fin K hK ι (Set.univ \ R) hRc hNames ρ hfin) δ
    (rv_label_cut_density K hK ι (Set.univ \ R) hRc hNames δ hδ)
  have hN := (native_coordinate_volume_family_gamma hc K hK ρ hfin δ hδ).row hc x
  have hNL := (native_coordinate_volume_family_gamma hc _ (gamma_rv_label_cut K hK ι R hR) ρ
    (rv_label_cut_fin K hK ι R hR hNames ρ hfin) δ (rv_label_cut_density K hK ι R hR hNames δ hδ)).row hc x
  have hNR := (native_coordinate_volume_family_gamma hc _ (gamma_rv_label_cut K hK ι (Set.univ \ R) hRc) ρ
    (rv_label_cut_fin K hK ι (Set.univ \ R) hRc hNames ρ hfin) δ
    (rv_label_cut_density K hK ι (Set.univ \ R) hRc hNames δ hδ)).row hc x
  let U : GammaVolumeObjects Bx (Cx.base : Set M) k := ⟨N.rowInContext x,hN⟩
  let A := (NL.rowInContext x).underlying.obj.domain
  have hA : A.carrier ⊆ U.val.underlying.obj.domain.carrier := fun _ h => h.1
  have hAΓ : GammaSetDefinable Bx {q : Point (M := M) 0 U.val.underlying.obj.arity | q.2 ∈ A.carrier} :=
    hNL.coordinates.domain
  have hPart := gammaVolumeBlowupClass_iso hc Cx Bx (U := (U.restrict A hA hAΓ).coprod (U.complement A hAΓ)) (V := U)
    (volumeComplementPartitionIso hc Cx U.val A hA)
    (gamma_actual_volume_complement_partition hc Cx U.val U.property A hA hAΓ)
  rw [← hPart,gammaVolumeBlowupClass_coprod]
  congr 1
  let P := U.complement A hAΓ
  let f : SpecialTransformations.DefinableGeometry.Map P.val.underlying.obj.domain
      (NR.rowInContext x).underlying.obj.domain :=
    SpecialTransformations.DefinableGeometry.Map.inclusion (fun _ h => ⟨h.1,Set.mem_univ _,fun hr => h.2 ⟨h.1,hr⟩⟩)
  have hf : Function.Bijective f :=
    ⟨fun s s' h => Subtype.ext (congrArg (fun w : (NR.rowInContext x).underlying.obj.domain => w.val) h),
      fun t => ⟨⟨t.val,t.property.1,fun h => t.property.2.2 h.2⟩,rfl⟩⟩
  have hCoord : ∀ s, (NR.rowInContext x).underlying.obj.value (f s) = P.val.underlying.obj.value s := fun _ => rfl
  have hForm : ∀ s, (NR.rowInContext x).form.value (f s) = P.val.form.value s := fun _ => rfl
  refine gammaVolumeBlowupClass_iso hc Cx Bx (RVVolumeIso.of_preserving_coordinates_full hc Cx
    (SpecialTransformations.Section4.rvFiniteIsoOfAmbient
      (SpecialTransformations.Section4.rvIsoOfVolumePreservingBijection f hf hCoord)) hCoord hForm) ?_
  exact gamma_volume_iso_of_full_map _ f (gamma_essential_volume_domain _ P.property.coordinates)
    (gamma_rv_coordinate_map hc _ id P.property.domain_graph (fun _ => rfl)) (fun _ => rfl)

end IntegrationInACVF.Section7
