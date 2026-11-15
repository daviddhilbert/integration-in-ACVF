import Integration7.AERVVolumeFunctionIntegrals
import Integration7.HeadAppendVolumeCoordinates

/-! The actual family obtained by contracting one VF head. Its selected
tuple consists of the old selected RV coordinates and the new head tag;
the original density remains a retained label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open SpecialTransformations.Section9
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {n a k : ℕ}

def nativeCoordinateVolumeFamily
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) (C.base : Set M) n a) (ρ : Fin (k+1) → Fin a)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero) :
    SelectedVFVolumeFamily C n a k where
  domain := rawSpecialSet hc A
  selected := ρ
  finite_selected := hfin
  form := mixedRetainedLabelVolumeForm (rawSpecialSet hc A) δ (fun p => hδ p.val p.property)

@[simp] theorem native_coordinate_volume_family_density
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) (C.base : Set M) n a) (ρ : Fin (k+1) → Fin a)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (p : (nativeCoordinateVolumeFamily hc A ρ hfin δ hδ).domain) :
    (nativeCoordinateVolumeFamily hc A ρ hfin δ hδ).form.value p = p.val.2 δ := rfl

def SelectedVFVolumeFamily.headIntegral
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (F : SelectedVFVolumeFamily C (n+1) a k)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain)) :
    SelectedVFVolumeFamily C n (1+T.arity) (k+1) :=
  nativeCoordinateVolumeFamily hc T.contractedSet (headAppendVolumeIndex T F.densityGraph.selected)
    (head_append_selected_fibres_finite C.uncountable.le C.saturated C.small T
      ((gammaLogicInput (⟨(C.base : Set M),Ξ⟩ : Base (M := M))).real_map_graph T.map)
      ((gammaLogicInput (⟨(C.base : Set M),Ξ⟩ : Base (M := M))).real_set _ (setDefinable T.target))
      F.densityGraph.selected F.densityGraph.finite_selected)
    (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) (Fin.last a)))
    (head_retained_density_nonzero T (Fin.last a) F.densityGraph_label_nonzero)

theorem SelectedVFVolumeFamily.headIntegral_density
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (F : SelectedVFVolumeFamily C (n+1) a k)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain))
    (p : (F.headIntegral hc Ξ T).domain) :
    (F.headIntegral hc Ξ T).form.value p =
      p.val.2 (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) (Fin.last a))) := rfl

theorem SelectedVFVolumeFamily.headIntegral_old_coordinates
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (F : SelectedVFVolumeFamily C (n+1) a k)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain)) (i : Fin (k+1)) :
    (F.headIntegral hc Ξ T).selected (Fin.castAdd 1 i) =
      Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) (F.densityGraph.selected i)) := by
  simp only [SelectedVFVolumeFamily.headIntegral,nativeCoordinateVolumeFamily,headAppendVolumeIndex,
    Fin.append_left, IntegrationInACVF.Section6.headSelectedLabelIndex]

theorem SelectedVFVolumeFamily.headIntegral_new_coordinate
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (F : SelectedVFVolumeFamily C (n+1) a k)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain)) :
    (F.headIntegral hc Ξ T).selected (Fin.last (k+1)) = (0 : Fin (1+T.arity)) := by
  change headAppendVolumeIndex T F.densityGraph.selected (Fin.natAdd (k+1) (0 : Fin 1)) = _
  simp only [headAppendVolumeIndex,Fin.append_right]
  rfl

end IntegrationInACVF.Section7
