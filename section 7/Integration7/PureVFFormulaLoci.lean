module

public import Integration7.PureVFDimensionUnions
public import Section9.MixedDifferentiationAE
public import Section3.GammaBaseTools

@[expose] public section

/-! Sorted VF formula loci are actual pure VF definable sets. Their
dimension is full exactly when they contain a tuple independent over the
original real parameter field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def pureVFFormulaLocus (R : Set (Fin n → M))
    (hR : DefinableOver S (fun _ => .vf) R) : DefSet (rawVFSpace (M := M) n) S := by
  refine ⟨{x | vfValues x ∈ R},?_⟩
  change S.Definable LRV ((rawVFSpace (M := M) n).preimage _)
  have hSet : (rawVFSpace (M := M) n).preimage {x | vfValues x ∈ R} = R := by
    ext z
    constructor
    · rintro ⟨hz,hr⟩
      have he : vfValues ((rawVFSpace (M := M) n).decode ⟨z,hz⟩) = z := Classical.choose_spec hz
      exact he ▸ hr
    · intro hz
      have hs : ∀ i, sortEval .vf (z i) := by
        obtain ⟨p,φ,hφ,hR⟩ := hR
        rw [hR] at hz
        exact hz.1
      let x : Fin n → VFType (M := M) := fun i => ⟨z i,hs i⟩
      have hp : z ∈ (rawVFSpace (M := M) n).domain := ⟨x,rfl⟩
      refine ⟨hp,?_⟩
      change vfValues ((rawVFSpace (M := M) n).decode ⟨z,hp⟩) ∈ R
      rw [show vfValues ((rawVFSpace (M := M) n).decode ⟨z,hp⟩) = z from Classical.choose_spec hp]
      exact hz
  rw [hSet]
  exact hR.raw_definable

theorem pure_vf_dimension_lt_of_no_independent
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0<n)
    (E : DefSet (rawVFSpace (M := M) n) (C.base : Set M))
    (hno : ∀ p : E, ¬ AlgebraicIndependent (vfParameterField (C.base : Set M)) p.val) :
    vfDim (rawRVSpace (M := M) 1) E < n := by
  rw [← pure_vf_graph_dimension E]
  apply mixed_vfDim_lt_of_no_independent hc C.saturated C.small _ (rawRVSpace_rvCoded 1) hn
  rintro ⟨p,x,hx⟩ hp
  apply hno x
  have he := congrArg Prod.fst hx
  change x.val = p.1 at he
  exact he.symm ▸ hp

theorem pure_vf_small_has_no_independent
    (hc : CanonicalStructure.IsCanonical (M := M))
    (E : DefSet (rawVFSpace (M := M) n) S)
    (hE : vfDim (rawRVSpace (M := M) 1) E < n) (p : E) :
    ¬ AlgebraicIndependent (vfParameterField S) p.val := by
  intro hp
  let q : (pureVFGraphMap E).image := ⟨(pureVFGraphMap E p).val,⟨p,rfl⟩⟩
  have hRank : vfTupleTrdeg S q.val.1 = (n : ℕ) :=
    (tupleField_trdeg_eq_arity_iff (vfParameterField S) p.val).mpr hp
  have hle := vfTupleTrdeg_le_vfDim hc (rawRVSpace (M := M) 1) (rawRVSpace_rvCoded 1)
    (pureVFGraphMap E).image q
  rw [hRank,pure_vf_graph_dimension E] at hle
  have hleNat : n ≤ vfDim (rawRVSpace (M := M) 1) E := by exact_mod_cast hle
  exact (Nat.not_le_of_lt hE) hleNat

end IntegrationInACVF.Section7
