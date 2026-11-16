module

public import Integration7.NativeRVLabelProducts
public import Integration7.PureRVLabelGraphMembership
public import Integration7.VolumeDensityGraphMembership
public import Integration7.IndependentRVGraphFactorizations
public import Integration7.ConstrainedUnarySources

@[expose] public section

/-! The density graph of an actual product with two retained densities
is precisely the unary source constrained by the corresponding pure-RV
product-density graph. No integral identity is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a d : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (R : DefSet (M := M) (C.base : Set M) 0 d) (δ : Fin a) (ε : Fin d)

def independentRVDensityConstraint : DefSet (M := M) (C.base : Set M) 0 ((a+d)+1) :=
  pureRVLabelGraph (independentRVLabelConstraint C Ξ hNames a R)
    (nativeRVLabelProduct hc (independentRVLabelConstraint C Ξ hNames a R) (Fin.natAdd a ε) (Fin.castAdd d δ))

theorem independent_rv_product_density_graph_source
    (A : SpecialTransformations.DefinableGeometry.DefSet (SpecialTransformations.Section4.rawMixedSpace (M := M) 1 a) (C.base : Set M))
    (ω : VolumeForm (mixedRVFactorDomain A (rawVolumeContractionLabels hc R)))
    (hω : ∀ q, ω.value q=q.val.2 (Fin.natAdd a ε)*q.val.2 (Fin.castAdd d δ)) :
    nativeMixedVolumeDomain hc (volumeDensityGraph ω) =
      constrainedUnarySource C Ξ hNames (nativeMixedVolumeDomain hc A)
        (independentRVDensityConstraint hc C Ξ hNames R δ ε) (Fin.castAdd 1 ∘ Fin.castAdd d) := by
  apply defSet_eq_of_carrier_eq
  ext p
  rw [constrained_unary_source_mem]
  change p ∈ (volumeDensityGraph ω).carrier ↔ _
  rw [mem_volume_density_graph]
  constructor
  · rintro ⟨q,hq,hDensity⟩
    have hm : (p.1,p.2 ∘ Fin.castAdd 1) ∈ (mixedRVFactorDomain A (rawVolumeContractionLabels hc R)).carrier := hq ▸ q.property
    rw [mem_mixed_rv_factor_domain,mem_rawVolumeContractionLabels] at hm
    refine ⟨hm.1,?_⟩
    apply (mem_pure_rv_label_graph _ _ _).mpr
    have hQ : (Fin.elim0,p.2 ∘ Fin.castAdd 1) ∈ carrier (independentRVLabelConstraint C Ξ hNames a R) :=
      (independent_rv_label_constraint_mem C Ξ hNames a R _).mpr hm.2
    let q₀ : independentRVLabelConstraint C Ξ hNames a R := ⟨(Fin.elim0,p.2 ∘ Fin.castAdd 1),hQ⟩
    refine ⟨q₀,rfl,?_⟩
    funext j
    have hj : j=(0 : Fin 1) := Subsingleton.elim _ _
    subst j
    apply Subtype.ext
    rw [native_rv_label_product_value]
    have hLabels := congrArg Prod.snd hq
    have hd := congrArg Subtype.val ((hω q).symm.trans hDensity)
    rw [SpecialTransformations.Section3.RVOperations.mul_val] at hd
    change iRVMul (p.2 (Fin.castAdd 1 (Fin.natAdd a ε))).val
      (p.2 (Fin.castAdd 1 (Fin.castAdd d δ))).val = (p.2 (Fin.last (a+d))).val
    simpa only [hLabels,Function.comp_apply] using hd
  · rintro ⟨hA,hGraph⟩
    obtain ⟨q₀,hq₀,hg⟩ := (mem_pure_rv_label_graph _ _ _).mp hGraph
    have hQ : (Fin.elim0,p.2 ∘ Fin.castAdd 1) ∈ carrier (independentRVLabelConstraint C Ξ hNames a R) := hq₀ ▸ q₀.property
    have hR := (independent_rv_label_constraint_mem C Ξ hNames a R _).mp hQ
    have hm : (p.1,p.2 ∘ Fin.castAdd 1) ∈ (mixedRVFactorDomain A (rawVolumeContractionLabels hc R)).carrier := by
      rw [mem_mixed_rv_factor_domain,mem_rawVolumeContractionLabels]
      exact ⟨hA,hR⟩
    let q : mixedRVFactorDomain A (rawVolumeContractionLabels hc R) := ⟨(p.1,p.2 ∘ Fin.castAdd 1),hm⟩
    refine ⟨q,rfl,?_⟩
    rw [hω]
    apply Subtype.ext
    rw [SpecialTransformations.Section3.RVOperations.mul_val]
    have hd := congrArg (fun t => (t (0 : Fin 1)).val) hg
    rw [native_rv_label_product_value] at hd
    have hLabels := congrArg Prod.snd hq₀
    change iRVMul (p.2 (Fin.castAdd 1 (Fin.natAdd a ε))).val
      (p.2 (Fin.castAdd 1 (Fin.castAdd d δ))).val = (p.2 (Fin.last (a+d))).val
    have hi : Fin.natAdd (a+d) (0 : Fin 1)=Fin.last (a+d) := by
      apply Fin.ext
      simp
    simpa only [hLabels,Function.comp_apply,hi] using hd
end IntegrationInACVF.Section7
