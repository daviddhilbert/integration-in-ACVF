import Integration7.PullbackVolumeMapDescent
import IntegrationSection5.RVContractionGamma
import Section4.FiniteMaps
import Section4.RVIsoTools

/-! A label-preserving bijection of full RV pullbacks descends when
the shared labels determine their RV fibres. The induced RV isomorphism
is constructed from the given VF map, so full lift-volume descent applies. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)

def finiteRVHomOfWeightPreserving {S : Set M} {n : ℕ} {U V : RVObject (M := M) S n}
    (hU : U.volume.FiniteFibres) (f : Map U.domain V.domain)
    (hWeight : ∀ u, rvWeight (U.value u) = rvWeight (V.value (f u))) : RVHom U V where
  map := f
  volumetric u := (hWeight u).le
  finite_volume_images t := by
    apply ((hU ⟨t,Set.mem_univ _⟩).image (fun a => V.value (f a))).subset
    rintro s ⟨a,ha,hs⟩
    exact ⟨a,Subtype.ext ha,hs⟩

def finiteRVIsoOfWeightPreservingBijection {S : Set M} {n : ℕ} {U V : RVObject (M := M) S n}
    (hU : U.volume.FiniteFibres) (hV : V.volume.FiniteFibres)
    (f : Map U.domain V.domain) (hf : Function.Bijective f)
    (hWeight : ∀ u, rvWeight (U.value u) = rvWeight (V.value (f u))) : U ≅ V where
  hom := finiteRVHomOfWeightPreserving hU f hWeight
  inv := finiteRVHomOfWeightPreserving hV (f.inverse hf) (by
    intro v
    have h := hWeight (f.inverse hf v)
    rw [Map.apply_inverse] at h
    exact h.symm)
  hom_inv_id := by apply RVHom.ext; apply Map.ext; intro u; exact Map.inverse_apply f hf u
  inv_hom_id := by apply RVHom.ext; apply Map.ext; intro v; exact Map.apply_inverse f hf v

variable {S : Set M} {n a b d : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) S n a}
variable {B : SpecialTransformations.Section5.DefSet (M := M) S n b}

theorem shared_labels_contractible
    (f : SpecialTransformations.Section5.Map A B) (ρ : Fin d → Fin a) (τ : Fin d → Fin b)
    (hB : ∀ p q : B, p.val.2 ∘ τ = q.val.2 ∘ τ → SpecialTransformations.Section5.SameRV p.val q.val)
    (hLabels : ∀ p : A, (f p).val.2 ∘ τ = p.val.2 ∘ ρ) :
    SpecialTransformations.Section5.Contractible f := by
  intro p q he
  apply hB
  rw [hLabels,hLabels]
  exact congrArg (fun r => r ∘ ρ) ((SpecialTransformations.Section5.sameRV_iff _ _).mp he).2

theorem shared_labels_inverse_contractible
    (f : SpecialTransformations.Section5.Map A B) (hf : Function.Bijective f)
    (ρ : Fin d → Fin a) (τ : Fin d → Fin b)
    (hA : ∀ p q : A, p.val.2 ∘ ρ = q.val.2 ∘ ρ → SpecialTransformations.Section5.SameRV p.val q.val)
    (hLabels : ∀ p : A, (f p).val.2 ∘ τ = p.val.2 ∘ ρ) :
    SpecialTransformations.Section5.Contractible (SpecialTransformations.Section5.Map.inverse f hf) := by
  apply shared_labels_contractible (SpecialTransformations.Section5.Map.inverse f hf) τ ρ hA
  intro q
  have h := hLabels (SpecialTransformations.Section5.Map.inverse f hf q)
  rw [SpecialTransformations.Section5.Map.apply_inverse] at h
  exact h.symm

omit hM in
theorem rv_weight_of_all_nonzero {n : ℕ} (t : Fin n → CanonicalRV.RVSort M)
    (ht : ∀ i, (t i).val ≠ iRVZero) : rvWeight t = n := by
  simp only [rvWeight,if_pos (ht _),Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]

def pullbackVolumeIsoOfLabelDeterminedMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {k a b d : ℕ}
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) a)
    (B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (k+1) b)
    (hA : SpecialTransformations.Section5.IsRVPullback (SpecialTransformations.Section5.carrier A))
    (hB : SpecialTransformations.Section5.IsRVPullback (SpecialTransformations.Section5.carrier B))
    (hAF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _
      (SpecialTransformations.Section5.rvObjectVolume (SpecialTransformations.Section5.pullbackObject A)))
    (hBF : @Map.FiniteFibres LRV M N _ _ (C.base : Set M) _ _
      (SpecialTransformations.Section5.rvObjectVolume (SpecialTransformations.Section5.pullbackObject B)))
    (δ : Fin a) (ε : Fin b)
    (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) (hε : ∀ p : B, (p.val.2 ε).val ≠ iRVZero)
    (ρ : Fin d → Fin a) (τ : Fin d → Fin b)
    (hSource : ∀ p q : A, p.val.2 ∘ ρ = q.val.2 ∘ ρ → SpecialTransformations.Section5.SameRV p.val q.val)
    (hTarget : ∀ p q : B, p.val.2 ∘ τ = q.val.2 ∘ τ → SpecialTransformations.Section5.SameRV p.val q.val)
    (hNZSource : ∀ p : A, ∀ i : Fin (k+1),
      (SpecialTransformations.Section5.rv (SpecialTransformations.Section5.vfAt p.val i)).val ≠ iRVZero)
    (hNZTarget : ∀ p : B, ∀ i : Fin (k+1),
      (SpecialTransformations.Section5.rv (SpecialTransformations.Section5.vfAt p.val i)).val ≠ iRVZero)
    (f : SpecialTransformations.Section5.Map A B) (hf : Function.Bijective f)
    (hLabels : ∀ p : A, (f p).val.2 ∘ τ = p.val.2 ∘ ρ)
    (hMeasure : PreservesVFVolume (rawPullbackVolumeForm hc A hA hAF δ hδ)
      (rawPullbackVolumeForm hc B hB hBF ε hε) (rawSpecialMap hc f)) :
    RVVolumeIso (pullbackCoordinateVolumeObject hc A hAF δ hδ)
      (pullbackCoordinateVolumeObject hc B hBF ε hε) := by
  let hC := shared_labels_contractible f ρ τ hTarget hLabels
  let hBack := shared_labels_inverse_contractible f hf ρ τ hSource hLabels
  let g := rvContractionMap f hC
  have hg := rvContractionMap_bijective f hf hC hBack
  let e : SpecialTransformations.Section5.pullbackObject A ≅ SpecialTransformations.Section5.pullbackObject B :=
    @finiteRVIsoOfWeightPreservingBijection M N (C.base : Set M) (k+1) _ _ hAF hBF g hg (by
      intro u
      obtain ⟨p,rfl⟩ := rawKeyImage_surjective A u
      change @rvWeight M N (k+1)
        (SpecialTransformations.Section5.rvObjectVolume (SpecialTransformations.Section5.pullbackObject A)
          (SpecialTransformations.Section5.Map.toImage (SpecialTransformations.Section5.rawKeyMap A) p)).val =
        @rvWeight M N (k+1)
        (SpecialTransformations.Section5.rvObjectVolume (SpecialTransformations.Section5.pullbackObject B)
          (rvContractionMap f hC (SpecialTransformations.Section5.Map.toImage
            (SpecialTransformations.Section5.rawKeyMap A) p))).val
      erw [pullbackObject_value_key,rvContractionMap_volume_spec]
      exact (@rv_weight_of_all_nonzero M N (k+1) _ (hNZSource p)).trans
        (@rv_weight_of_all_nonzero M N (k+1) _ (hNZTarget (f p))).symm)
  exact pullbackVolumeIsoOfCompatibleMap hc C A B hA hB hAF hBF δ ε hδ hε f hf e
    (fun p => rvContractionMap_spec f hC p) hMeasure

end IntegrationInACVF.Section7
