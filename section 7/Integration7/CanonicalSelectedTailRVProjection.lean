import Integration7.SelectedRVVFTailProgramProjections
import IntegrationSection5.OrderedContractionProgram
import IntegrationSection6.MixedCoordinatePointMaps

/-! A contractible full contraction of a selected-label VF tail gives
a genuine bijection of its final RV labels with the original RV source.
The map is the literal projection onto retained old labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {a d r : ℕ}

def canonicalSelectedTailRVProjection (hc : CanonicalStructure.IsCanonical (M := M))
    (U : DefSet (M := M) S 0 a) (ρ : Fin d → Fin a) {V : DefSet (M := M) S 0 r}
    (E : OrderedContractionProgram S (nativeProgramSelectedRVVFTailLift (n := 0) (d := d) hc U ρ) V) :
    SpecialTransformations.Section5.Map V U := by
  let R := mixedCoordinatePointMap (id : Fin 0 → Fin 0) (suffixIndex E.rvArity_le) S
  let G := SpecialTransformations.Section5.Map.comp R
    (SpecialTransformations.Section5.Map.inclusion (show carrier V ⊆
      carrier (PresentedSet.univ (pointSpace (M := M) 0 r) S) from fun _ _ => Set.mem_univ _))
  refine mapIntoSubset G U ?_
  intro v
  obtain ⟨p,hp⟩ := E.surjective v
  have hRV : v.val.2 ∘ suffixIndex E.rvArity_le = p.val.2 := by
    funext j
    have h := E.oldLabels p j
    rwa [hp] at h
  have hVF : v.val.1 ∘ id = (Fin.elim0 : Fin 0 → VF (M := M)) := funext (fun j => j.elim0)
  change (v.val.1 ∘ id,v.val.2 ∘ suffixIndex E.rvArity_le) ∈ carrier U
  rw [hRV,hVF]
  exact ((native_program_selected_zero_tail_carrier hc U ρ p.val).mp p.property).1

theorem canonical_selected_tail_rv_projection_labels
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U : DefSet (M := M) S 0 a) (ρ : Fin d → Fin a) {V : DefSet (M := M) S 0 r}
    (E : OrderedContractionProgram S (nativeProgramSelectedRVVFTailLift (n := 0) (d := d) hc U ρ) V)
    (v : V) :
    (canonicalSelectedTailRVProjection hc U ρ E v).val.2 = v.val.2 ∘ suffixIndex E.rvArity_le := rfl

theorem canonical_selected_tail_rv_projection_after
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U : DefSet (M := M) S 0 a) (ρ : Fin d → Fin a) {V : DefSet (M := M) S 0 r}
    (E : OrderedContractionProgram S (nativeProgramSelectedRVVFTailLift (n := 0) (d := d) hc U ρ) V)
    (p : nativeProgramSelectedRVVFTailLift (n := 0) (d := d) hc U ρ) :
    canonicalSelectedTailRVProjection hc U ρ E (E.toMap p) = nativeProgramSelectedRVVFTailProjection hc U ρ p := by
  apply Subtype.ext
  rw [native_program_selected_rv_vf_tail_projection_value]
  refine Prod.ext (by funext j; exact j.elim0) ?_
  exact funext (fun j => E.oldLabels p j)

theorem canonical_selected_tail_rv_projection_bijective
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U : DefSet (M := M) S 0 a) (ρ : Fin d → Fin a) {V : DefSet (M := M) S 0 r}
    (E : OrderedContractionProgram S (nativeProgramSelectedRVVFTailLift (n := 0) (d := d) hc U ρ) V)
    (hCon : Contractible E.toMap) : Function.Bijective (canonicalSelectedTailRVProjection hc U ρ E) := by
  constructor
  · intro v w he
    obtain ⟨p,hp⟩ := E.surjective v
    obtain ⟨q,hq⟩ := E.surjective w
    have hOld := congrArg (fun t : U => t.val.2) he
    rw [canonical_selected_tail_rv_projection_labels,canonical_selected_tail_rv_projection_labels] at hOld
    have hLabels : p.val.2 = q.val.2 := by
      funext j
      have h := congrFun hOld j
      have hp' := E.oldLabels p j
      have hq' := E.oldLabels q j
      rw [hp] at hp'
      rw [hq] at hq'
      exact hp'.symm.trans (h.trans hq')
    have hSame := hCon p q (native_program_selected_zero_tail_same_rv hc U ρ p q hLabels)
    rw [hp,hq] at hSame
    exact Subtype.ext (Prod.ext (by funext j; exact j.elim0) ((sameRV_iff _ _).mp hSame).2)
  · intro u
    obtain ⟨p,hp⟩ := native_program_selected_rv_vf_tail_projection_surjective hc U ρ u
    exact ⟨E.toMap p,(canonical_selected_tail_rv_projection_after hc U ρ E p).trans hp⟩

end IntegrationInACVF.Section7
