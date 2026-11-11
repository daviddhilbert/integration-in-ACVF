import IntegrationSection5.FiniteMapSupport
import IntegrationSection5.StandardContractionLift
import Section4.RVWeightDimension
import Section4.ModelGeometry

/-! A definable injection into one VF coordinate excludes two independent
nonzero RV directions. Finite formula support supplies the small internal
real base; no smallness of the given working code set is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
namespace IntegrationInACVF.Section5.InternalDimension
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section4
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n r m : ℕ}

theorem unary_polydisc_bound (hcan : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (t : Fin n → CanonicalRV.RVSort M) (s : Fin r → CanonicalRV.RVSort M)
    (hA : ∀ q, q ∈ A.carrier ↔ tupleRV q.1 = t ∧ q.2 = s)
    (f : Map A (DefSet.univ (rawMixedSpace 1 m) S)) (hf : Function.Injective f) :
    rvWeight t ≤ 1 := by
  obtain ⟨R,hR,_,hAR,hfR⟩ := finite_map_support f
  let A' : DefSet (rawMixedSpace (M := M) n r) R := ⟨A.carrier,hAR⟩
  let g : Map A' (DefSet.univ (rawMixedSpace 1 m) R) :=
    ⟨fun a => ⟨(f ⟨a.val,a.property⟩).val,Set.mem_univ _⟩,hfR⟩
  have hg : Function.Injective g := by
    intro a b hab
    have hv := congrArg (fun q : DefSet.univ (rawMixedSpace (M := M) 1 m) R => q.val) hab
    have he := hf (Subtype.ext hv)
    exact Subtype.ext (congrArg Subtype.val he)
  have hRsmall : Cardinal.mk R < κ := hR.lt_aleph0.trans_le hκ
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  letI : Valued (VFType (M := M)) Γ := Valued.mk' v
  let Δ := rawRVSpace (M := M) 0
  have hΔ := rawRVSpace_rvCoded (M := M) 0
  have hdim := vfDim_rv_polydisc hcan hs hRsmall Δ hΔ hv A' t s hA
  rw [← hdim]
  exact (vfDim_le_of_finite_map Δ g (Map.finiteFibres_of_injective hg)).trans
    (vfDim_le_arity Δ (DefSet.univ (rawMixedSpace 1 m) R))

end IntegrationInACVF.Section5.InternalDimension

namespace IntegrationInACVF.Section5
open SpecialTransformations.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n r m : ℕ}

theorem unary_injection_polydisc_weight_le {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (A : PresentedSet (rawPointSpace (M := M) n r) S)
    (t : Fin n → RV (M := M)) (s : Fin r → RV (M := M))
    (hA : ∀ q, q ∈ carrier A ↔
      @SpecialTransformations.Section4.tupleRV M (@CanonicalStructure.normalize M sM)
        (CanonicalStructure.normalized_model hM) n q.1 = t ∧ q.2 = s)
    (f : Map A (PresentedSet.univ (rawPointSpace 1 m) S)) (hf : Function.Injective f) :
    @SpecialTransformations.Section4.rvWeight M (@CanonicalStructure.normalize M sM) n t ≤ 1 :=
  @InternalDimension.unary_polydisc_bound M (@CanonicalStructure.normalize M sM)
    (CanonicalStructure.normalized_model hM) S n r m
    (@CanonicalStructure.normalize_isCanonical M sM) κ hκ hs.normalize A t s hA f hf

end IntegrationInACVF.Section5
