import IntegrationSection5.StandardContractionNormalization
import IntegrationSection5.NaturalContractionGamma

/-! Original-Gamma certificates for the normalized first-coordinate RV
object and the complete natural lift graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5.StandardContraction
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {P : GammaParameters.Base (M := M)} {S : Set M}
variable {n m : ℕ} {A : DefSet (M := M) S n m} {σ : Equiv.Perm (Fin n)}

theorem gamma_normalized_domain (C : StandardContraction A σ)
    (hU : GammaSetDefinable P (carrier C.target)) :
    GammaSetDefinable P {p : Point (M := M) 0 (n+C.arity) |
      p.2 ∈ carrier (rvObjectDomain C.normalizedObject)} := by
  have h := (gammaLogicInput P).image_real
    (rvCoordinatePointMap (prependVolumeIndex C.volumeIndex) P.real) hU
  convert h using 1
  ext p
  constructor
  · intro hp
    obtain ⟨v,hv⟩ := hp
    obtain ⟨u,hu⟩ := v.property
    refine ⟨⟨u.val,Set.mem_univ _⟩,u.property,?_⟩
    refine Prod.ext (Subsingleton.elim _ _) ?_
    change u.val.2 ∘ prependVolumeIndex C.volumeIndex = p.2
    change v.val ∘ prependVolumeIndex C.volumeIndex = p.2 at hv
    have hu' : u.val.2 = v.val := hu
    rw [hu']
    exact hv
  · rintro ⟨u,hu,he⟩
    refine ⟨Map.toImage (rawLabelMap C.target) ⟨u.val,hu⟩,?_⟩
    exact congrArg Prod.snd he

def gammaNormalizedObject (hPS : P.real ⊆ S) (C : StandardContraction A σ)
    (hU : GammaSetDefinable P (carrier C.target)) : GammaRVObject P n where
  codes := S
  real_contains := hPS
  object := C.normalizedObject
  domain_graph := C.gamma_normalized_domain hU
  volume_graph := by
    let g := rvCoordinatePointMap (Fin.castAdd C.arity : Fin n → Fin (n+C.arity)) P.real
    apply GammaGraphDefinable.congr ((gammaLogicInput P).restrict_graph
      (C.gamma_normalized_domain hU) ((gammaLogicInput P).real_map_graph g))
    intro p q
    constructor
    · rintro ⟨hp,x,hx,hq⟩
      refine ⟨⟨p.2,hp⟩,rfl,?_⟩
      exact (congrArg (fun z : Point (M := M) 0 (n+C.arity) => z.2 ∘ Fin.castAdd C.arity) hx).symm.trans
        (congrArg Prod.snd hq)
    · rintro ⟨x,hx,hq⟩
      refine ⟨(show p.2 ∈ carrier (rvObjectDomain C.normalizedObject) from hx ▸ x.property),
        ⟨p,Set.mem_univ _⟩,rfl,?_⟩
      exact Prod.ext (Subsingleton.elim _ _)
        ((congrArg (fun t => t ∘ Fin.castAdd C.arity) hx).symm.trans hq)

theorem gamma_normalized_natural_graph (hPS : P.real ⊆ S) (C : StandardContraction A σ)
    (hA : GammaSetDefinable P (carrier A)) (hC : GammaProgramDefinable P C.program) :
    GammaGraphDefinable P (fun (p : Point (M := M) n m) (q : Point (M := M) n (n+C.arity)) =>
      ∃ a : A, a.val = p ∧ (C.normalizedNaturalLiftMap a).val = q) := by
  have h := gamma_postcompose_real (gammaLogicInput P) C.naturalMap
    (gamma_standard_natural_graph hPS C hA hC)
    (canonicalMap (PresentedSet.univ (pointSpace (M := M) n C.arity) P.real)) hPS
  apply GammaGraphDefinable.congr h
  intro p q
  rfl

/-- The normalized natural bijection is an actual original-Gamma isomorphism
onto the lift of the RV object with volume in its first n coordinates. -/
def gammaNormalizedLiftIso (hPS : P.real ⊆ S) (C : StandardContraction A σ)
    (hA : GammaSetDefinable P (carrier A)) (hC : GammaProgramDefinable P C.program) :
    GammaIso P (carrier A) (C.gammaNormalizedObject hPS (gamma_program_final_set C.program hC)).lift where
  equiv := Equiv.ofBijective C.normalizedNaturalLiftMap C.normalizedNaturalLiftMap_bijective
  graph := C.gamma_normalized_natural_graph hPS hA hC

end IntegrationInACVF.Section5.StandardContraction
