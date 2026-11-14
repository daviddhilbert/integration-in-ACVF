import Integration7.GammaTermClosureRVMaps
import Integration7.GammaVolumeParameterGeometry

/-! Ordinary volume geometry over exactly the term closure of the real
base has full original-Gamma graphs and original-base algebraic centers. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {a b k n : ℕ}

theorem gamma_rv_map_graph_of_parameter_closure
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hS : S = (Substructure.closure LRV B.real : Set M))
    {A : DefSet (rawRVSpace (M := M) a) S} {D : DefSet (rawRVSpace (M := M) b) S}
    (f : Map A D) : RVMapGamma f B := by
  subst S
  exact gamma_rv_map_graph_of_term_closure hc f

theorem VolumeObjectGamma.of_term_context
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hBase : (C.base : Set M) = (Substructure.closure LRV B.real : Set M))
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) : VolumeObjectGamma U B :=
  ⟨gamma_rv_map_graph_of_parameter_closure hc hBase _,gamma_rv_map_graph_of_parameter_closure hc hBase _⟩

theorem RVVolumeIso.gamma_of_term_context
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hBase : (C.base : Set M) = (Substructure.closure LRV B.real : Set M))
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (e : RVVolumeIso U V) : e.GammaDefinable B :=
  gamma_rv_map_graph_of_parameter_closure hc hBase (finiteIsoMap e.iso)

theorem BlowupAdmissible.gamma_of_term_context
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hBase : (C.base : Set M) = (Substructure.closure LRV B.real : Set M))
    {U : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (h : BlowupAdmissible U) :
    GammaBlowupCenter U B := by
  intro u
  obtain ⟨W,hW,hWf,hu⟩ := coordinate_algebraic_termContext hc C B.real hBase (Fin.last k)
    (U.underlying.obj.value u) (h.algebraic u)
  exact ⟨W,real_definableAtBase _ .rv W hW,hWf,hu⟩

theorem VolumeBlowup.gamma_of_term_context
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hBase : (C.base : Set M) = (Substructure.closure LRV B.real : Set M))
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (b : VolumeBlowup U V) : b.GammaDefinable B :=
  ⟨.of_term_context hc C hBase _,.of_term_context hc C hBase _,.of_term_context hc C hBase _,
    gamma_rv_map_graph_of_parameter_closure hc hBase _,
    b.elementary.admissible.gamma_of_term_context hc C hBase,
    b.sourceIso.gamma_of_term_context hc C hBase,b.targetIso.gamma_of_term_context hc C hBase⟩

theorem iterated_volume_blowup_gamma_in_term_context
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hBase : (C.base : Set M) = (Substructure.closure LRV B.real : Set M))
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (g : IteratedVolumeBlowup n U V) :
    GammaIteratedVolumeBlowup B (C.base : Set M) k n
      ⟨U,.of_term_context hc C hBase U⟩ ⟨V,.of_term_context hc C hBase V⟩ := by
  induction g with
  | refl U => exact .refl _
  | @step n U V W b rest ih =>
    obtain ⟨b⟩ := b
    exact .step (V := ⟨V,.of_term_context hc C hBase V⟩) ⟨b,b.gamma_of_term_context hc C hBase⟩ ih

theorem volume_common_gamma_in_term_context
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hBase : (C.base : Set M) = (Substructure.closure LRV B.real : Set M))
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (g : VolumeBlowupEquivalent U V) :
    GammaVolumeBlowupEquivalent B (C.base : Set M) k
      ⟨U,.of_term_context hc C hBase U⟩ ⟨V,.of_term_context hc C hBase V⟩ := by
  obtain ⟨m,n,U',V',hU,hV,⟨e⟩⟩ := g
  exact ⟨m,n,⟨U',.of_term_context hc C hBase U'⟩,⟨V',.of_term_context hc C hBase V'⟩,
    iterated_volume_blowup_gamma_in_term_context hc C hBase hU,
    iterated_volume_blowup_gamma_in_term_context hc C hBase hV,e,e.gamma_of_term_context hc C hBase⟩

end IntegrationInACVF.Section7
