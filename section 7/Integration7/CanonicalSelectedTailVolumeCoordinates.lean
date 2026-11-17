module

public import Integration7.CanonicalSelectedTailRVProjection
public import IntegrationSection5.NaturalContractionMap
public import IntegrationSection6.GammaFamilyCoordinates

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The canonical selected-tail label projection keeps its complete
Gamma graph and identifies the tail's VF volume tuple literally with
the original selected RV tuple. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {a d r : ℕ}

theorem gamma_canonical_selected_tail_rv_projection
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U : DefSet (M := M) S 0 a) (ρ : Fin d → Fin a) {V : DefSet (M := M) S 0 r}
    (E : OrderedContractionProgram S (nativeProgramSelectedRVVFTailLift (n := 0) (d := d) hc U ρ) V)
    (hV : GammaSetDefinable G (carrier V)) :
    GammaGraphDefinable G (pointMapGraph (canonicalSelectedTailRVProjection hc U ρ E)) := by
  let R := mixedCoordinatePointMap (id : Fin 0 → Fin 0) (suffixIndex E.rvArity_le) G.real
  apply GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph hV (gamma_global_map_graph R))
  intro p q
  constructor
  · rintro ⟨hp,hq⟩
    refine ⟨⟨p,hp⟩,rfl,?_⟩
    exact hq
  · rintro ⟨v,rfl,hq⟩
    exact ⟨v.property,hq⟩

theorem canonical_selected_tail_volume_coordinates
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U : DefSet (M := M) S 0 a) (ρ : Fin d → Fin a) {V : DefSet (M := M) S 0 r}
    (E : OrderedContractionProgram S (nativeProgramSelectedRVVFTailLift (n := 0) (d := d) hc U ρ) V)
    (hVF : ∀ p, (E.naturalMap p).val.1 = p.val.1) (v : V) (j : Fin d) :
    v.val.2 (E.volumeIndex j) = (canonicalSelectedTailRVProjection hc U ρ E v).val.2 (ρ j) := by
  obtain ⟨p,rfl⟩ := E.surjective v
  rw [E.naturalMap_rv]
  change rv ((E.naturalMap p).val.1 j) = _
  rw [hVF p,canonical_selected_tail_rv_projection_labels]
  have hP := ((native_program_selected_zero_tail_carrier hc U ρ p.val).mp p.property).2
  exact (congrFun hP j).trans (E.oldLabels p (ρ j)).symm

end IntegrationInACVF.Section7
