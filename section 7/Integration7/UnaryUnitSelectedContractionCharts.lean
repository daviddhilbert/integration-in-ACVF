import Integration7.PointPrefixedVolumeObjects
import Integration7.UnaryRawSelectedVolumeCharts
import Integration7.SelectedFamilyStandardVolumeComparison
import IntegrationSection6.StandardProgramPresentations

/-! Selecting a retained unit label before a unary contraction gives
the degree-one point times its ordinary raw contraction object. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (VF RV carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a : ℕ}
variable {S : Set M} {A : SpecialTransformations.Section5.DefSet (M := M) S 1 a}

theorem unary_standard_retained_unit (T : StandardContraction A (Equiv.refl _)) (δ : Fin a)
    (hOne : ∀ p ∈ carrier A, p.2 δ=(1 : CanonicalRV.RVSort M)) (q : T.target) :
    q.val.2 (suffixIndex T.program.rvArity_le δ)=(1 : CanonicalRV.RVSort M) := by
  obtain ⟨p,hp⟩ := T.program.surjective q
  have h := T.program.oldLabels p δ
  rw [hp] at h
  have hCarrier := congrArg carrier (vfPermutationImage_id_eq A)
  have hm : p.val ∈ carrier A := (Set.ext_iff.mp hCarrier p.val).mp p.property
  exact h.trans (hOne p.val hm)

theorem unary_standard_empty_selected_index (T : StandardContraction A (Equiv.refl _)) :
    selectedStandardVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)=T.volumeIndex := by
  funext i
  change Fin.append T.volumeIndex (suffixIndex T.program.rvArity_le ∘ Fin.elim0)
    (finCongr (Nat.add_comm 0 1) i)=T.volumeIndex i
  have hi : finCongr (Nat.add_comm 0 1) i=Fin.castAdd 0 i := Fin.ext rfl
  rw [hi,Fin.append_left]

variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M)))
variable (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a)
variable (hfin : ∀ x : Fin 1 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
variable (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
variable (hOne : ∀ p ∈ carrier A, p.2 δ=(1 : CanonicalRV.RVSort M))
variable (T : StandardContraction A (Equiv.refl _))

def unaryUnitSelectedPointPrefixIso :
    RVVolumeIso
      (standardAppendVolumeObject hc C Ξ A (fun _ : Fin 1 => δ) δ hδ
        (fun x _ => (hfin x).subset (fun _ h => h.1)) T)
      (pointPrefixedVolumeObject C (selectedStandardVolumeObject hc C Ξ A (Fin.elim0 : Fin 0 → Fin a) δ hδ
        (fun x _ => (hfin x).subset (fun _ h => h.1)) T)) := by
  let U := standardAppendVolumeObject hc C Ξ A (fun _ : Fin 1 => δ) δ hδ
    (fun x _ => (hfin x).subset (fun _ h => h.1)) T
  let W := selectedStandardVolumeObject hc C Ξ A (Fin.elim0 : Fin 0 → Fin a) δ hδ
    (fun x _ => (hfin x).subset (fun _ h => h.1)) T
  let V := pointPrefixedVolumeObject C W
  have hUV : U.underlying.obj.domain.carrier=V.underlying.obj.domain.carrier := rfl
  have hIndex : orderedAppendVolumeIndex T.program (fun _ : Fin 1 => δ) =
      Fin.append (fun _ : Fin 1 => suffixIndex T.program.rvArity_le δ) T.volumeIndex := by
    funext i
    have h := congrFun (standard_append_volume_index_closed T (fun _ : Fin 1 => δ)) i
    have hi : (finCongr (append_volume_length_eq 1 0)).symm i=i := Fin.ext rfl
    have hVol : T.volumeIndex ∘ (Equiv.refl (Fin 1))=T.volumeIndex := rfl
    rw [hVol] at h
    simpa only [Function.comp_apply,hi] using h
  have hCoord (u : U.underlying.obj.domain) :
      V.underlying.obj.value ⟨u.val,hUV.le u.property⟩=U.underlying.obj.value u := by
    let q : T.target := ⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc T.target u.val).mp u.property⟩
    change Fin.append (fun _ : Fin 1 => 1)
      (u.val ∘ selectedStandardVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) =
        u.val ∘ orderedAppendVolumeIndex T.program (fun _ : Fin 1 => δ)
    rw [unary_standard_empty_selected_index,hIndex]
    funext i
    refine Fin.addCases (m := 1) (n := 1) (fun j => ?_) (fun j => ?_) i
    · simp only [Function.comp_apply,Fin.append_left]
      exact (unary_standard_retained_unit T δ hOne q).symm
    · simp only [Function.comp_apply,Fin.append_right]
  have hForm (u : U.underlying.obj.domain) : V.form.value ⟨u.val,hUV.le u.property⟩=U.form.value u := by
    change u.val (suffixIndex T.program.rvArity_le δ)=u.val (orderedAppendDensityIndex T.program δ)
    rw [standard_append_density_index]
  let e : U.underlying ≅ V.underlying := rvFiniteIsoOfAmbient (U := U.underlying) (V := V.underlying)
    (rvIsoOfCarrierEq U.underlying.obj.domain V.underlying.obj.domain U.underlying.obj.volume V.underlying.obj.volume hUV hCoord)
  exact RVVolumeIso.of_preserving_coordinates_full hc C e hCoord hForm

def unaryUnitSelectedRawProductIso :
    RVVolumeIso
      (standardAppendVolumeObject hc C Ξ A (fun _ : Fin 1 => δ) δ hδ
        (fun x _ => (hfin x).subset (fun _ h => h.1)) T)
      ((degreeOnePointVolumeObject (C.base : Set M)).prod (rawStandardVolumeObject hc C Ξ A hfin δ hδ T)) :=
  (unaryUnitSelectedPointPrefixIso hc C Ξ A hfin δ hδ hOne T).trans hc C
    ((pointPrefixedVolumeIso C _ hc).trans hc C
      ((RVVolumeIso.refl hc C (degreeOnePointVolumeObject (C.base : Set M))).prod hc C
        (unaryRawSelectedVolumeIso hc C Ξ A hfin δ hδ T)))
end IntegrationInACVF.Section7
