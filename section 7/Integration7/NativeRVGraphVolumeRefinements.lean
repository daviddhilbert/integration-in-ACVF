import Integration7.NativeVolumeDomains
import Integration7.GammaRVGraphRefinementGeometry
import Integration7.VFVolumeBijections
import Integration7.MixedRetainedLabelVolumeForms

/-! Graph refinement is an actual VF-volume bijection for every
transported density. A retained coordinate density stays the same literal
old RV coordinate, without a constancy assumption on that density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9 SpecialTransformations.Section5
open IntegrationInACVF.Section4

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {k m d : ℕ}

def nativeMixedVFVolumeObject (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S (k+1) m)
    (hfin : ∀ x : Fin (k+1) → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (ω : VolumeForm (rawSpecialSet hc A)) : PositiveVFVolumeObject (M := M) S k where
  arity := m
  domain := rawSpecialSet hc A
  finite_labels := hfin
  form := ω

def nativeRVGraphVolumeRefinement (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (M := M) S (k+1) m)
    (hfin : ∀ x : Fin (k+1) → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (P : GammaRVMap G (carrier A) d) (hNames : commonRealNames G ⊆ S)
    (ω : VolumeForm (rawSpecialSet hc A)) : PositiveVFVolumeObject (M := M) S k :=
  nativeMixedVFVolumeObject hc (gammaRVGraphRefinement A P hNames)
    (gamma_rv_graph_refinement_finite_labels A hfin P hNames)
    (ω.pullback (rawSpecialMap hc (Map.inverse (Map.toImage (gammaRVGraphRefinementMap A P hNames))
      (gamma_rv_graph_refinement_bijective A P hNames))))

def nativeRVGraphVolumeBijection (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (A : DefSet (M := M) (C.base : Set M) (k+1) m)
    (hfin : ∀ x : Fin (k+1) → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (P : GammaRVMap G (carrier A) d) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (ω : VolumeForm (rawSpecialSet hc A)) :
    VFVolumeBijection (nativeMixedVFVolumeObject hc A hfin ω) (nativeRVGraphVolumeRefinement hc A hfin P hNames ω) := by
  let f := Map.toImage (gammaRVGraphRefinementMap A P hNames)
  let hf := gamma_rv_graph_refinement_bijective A P hNames
  apply VFVolumeBijection.of_preserving_vf_and_density hc C (rawSpecialMap hc f) hf (fun _ => rfl)
  intro p
  change ω.value p = ω.value (rawSpecialMap hc (Map.inverse f hf) (rawSpecialMap hc f p))
  apply congrArg ω.value
  apply Subtype.ext
  have hv := congrArg Subtype.val (Map.inverse_apply f hf ⟨p.val,p.property⟩)
  exact hv.symm

theorem native_rv_graph_refinement_inverse_value (A : DefSet (M := M) S (k+1) m)
    (P : GammaRVMap G (carrier A) d) (hNames : commonRealNames G ⊆ S)
    (q : gammaRVGraphRefinement A P hNames) :
    (Map.inverse (Map.toImage (gammaRVGraphRefinementMap A P hNames))
      (gamma_rv_graph_refinement_bijective A P hNames) q).val = retainVFLabels (Fin.castAdd d) q.val := by
  obtain ⟨p,rfl⟩ := (gamma_rv_graph_refinement_bijective A P hNames).2 q
  rw [Map.inverse_apply]
  exact (gamma_rv_graph_refinement_retains_labels A P hNames p).symm

theorem native_rv_graph_refinement_retained_density
    (hc : CanonicalStructure.IsCanonical (M := M)) (A : DefSet (M := M) S (k+1) m)
    (hfin : ∀ x : Fin (k+1) → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (P : GammaRVMap G (carrier A) d) (hNames : commonRealNames G ⊆ S)
    (ω : VolumeForm (rawSpecialSet hc A)) (δ : Fin m) (hω : ∀ p, ω.value p = p.val.2 δ)
    (q : (nativeRVGraphVolumeRefinement hc A hfin P hNames ω).domain) :
    (nativeRVGraphVolumeRefinement hc A hfin P hNames ω).form.value q = q.val.2 (Fin.castAdd d δ) := by
  change ω.value (rawSpecialMap hc (Map.inverse (Map.toImage (gammaRVGraphRefinementMap A P hNames))
    (gamma_rv_graph_refinement_bijective A P hNames)) q) = _
  rw [hω]
  have hv := native_rv_graph_refinement_inverse_value A P hNames ⟨q.val,q.property⟩
  exact congrArg (fun p : Point (M := M) (k+1) m => p.2 δ) hv

end IntegrationInACVF.Section7
