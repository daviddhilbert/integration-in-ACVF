import IntegrationSection6.RootSelection

/-! Construct a genuine inherited full-locus focus from the uniquely
solvable, definable root set, retaining its full function graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section6

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

def rootVFCoordinateMap (S : Set M) (j : Fin n) :
    Map (PresentedSet.univ (SpecialTransformations.Section4.vfSpace (M := M) n) S)
      (PresentedSet.univ (SpecialTransformations.Section4.vfSpace 1) S) :=
  Map.ofCodes _ (fun a => ![a j]) (fun z => fun _ => z j)
    (fun _ => rawProj S j) (fun c => fun _ => c.property j)
    (by intro c; funext i; fin_cases i; rfl)

theorem erase_other_eq {j : Fin n} {p q : Point (M := M) n m}
    (he : erase j p = erase j q) (i : Fin n) (hi : i ≠ j) : p.1 i = q.1 i := by
  have h := congrArg (fun z : Point (M := M) n m => z.1 i) he
  simpa [erase, replace, hi] using h

theorem tagged_erase_sameRV {A : Set (Point (M := M) n m)} {j : Fin n} {k : Fin m}
    (htag : Tagged A j k) {p q : Point (M := M) n m}
    (hp : p ∈ A) (hq : q ∈ A) (he : erase j p = erase j q) : SameRV p q := by
  have hl' := congrArg (fun z : Point (M := M) n m => z.2) he
  have hl : p.2 = q.2 := hl'
  apply (sameRV_iff _ _).mpr
  refine ⟨?_,hl⟩
  intro i
  by_cases hi : i = j
  · subst i
    exact (htag p hp).symm.trans ((congrFun hl k).trans (htag q hq))
  · exact congrArg rv (erase_other_eq he i hi)

variable (A : DefSet (M := M) S n m) (R : Set (Fin n → M))
variable (j : Fin n) (k : Fin m)
variable (hcover : ∀ p ∈ carrier A,
  (fun i => (rv (p.1 i)).val) ∈ @rootDomain M (@CanonicalStructure.normalize M sM) n R j)
variable (hR : @Set.Definable M S LRV (@CanonicalStructure.normalize M sM) (Fin n) R)

include hcover hR

private def rootCenter (p : Point (M := M) n m) : VF (M := M) :=
  if hp : p ∈ carrier A then (rootSelectionMap A R j hcover hR ⟨p,hp⟩).val j else 0

private theorem rootCenter_rv (p : Point (M := M) n m) (hp : p ∈ carrier A) :
    rv (rootCenter A R j hcover hR p) = rv (p.1 j) := by
  simp only [rootCenter, dif_pos hp]
  exact (rootSelectionMap_spec A R j hcover hR ⟨p,hp⟩).2.2.1 j

private theorem rootCenter_independent (htag : Tagged (carrier A) j k)
    (p q : Point (M := M) n m) (hp : p ∈ carrier A) (hq : q ∈ carrier A)
    (he : erase j p = erase j q) :
    rootCenter A R j hcover hR p = rootCenter A R j hcover hR q := by
  have hs := (sameRV_iff _ _).mp (tagged_erase_sameRV htag hp hq he)
  let b := (rootSelectionMap A R j hcover hR ⟨p,hp⟩).val
  let c := (rootSelectionMap A R j hcover hR ⟨q,hq⟩).val
  have hb := rootSelectionMap_spec A R j hcover hR ⟨p,hp⟩
  have hc := rootSelectionMap_spec A R j hcover hR ⟨q,hq⟩
  have hcp : rootSelectorRelation A R j p c := by
    refine ⟨hp,hc.2.1,fun i => (hc.2.2.1 i).trans (hs.1 i).symm,?_⟩
    intro i hi
    exact (hc.2.2.2 i hi).trans (erase_other_eq he i hi).symm
  have hbc := rootSelector_unique A R j hcover p b c hb hcp
  simpa only [rootCenter, dif_pos hp, dif_pos hq] using congrFun hbc j

/-- The focus is on the whole source, with a graph over precisely S. -/
def rootFocus (hA : IsRVPullback (carrier A)) (htag : Tagged (carrier A) j k) :
    Focus A j k where
  tagged := htag
  locus := carrier A
  locus_pullback := hA
  locus_subset := subset_hull _
  center := rootCenter A R j hcover hR
  independent := fun p hp q hq he => rootCenter_independent A R j k hcover hR htag p q hp.1 hq.1 he
  center_mem := by
    intro p hp
    apply (isRVPullback_iff _).mp hA p hp.1
    apply (sameRV_iff _ _).mpr
    refine ⟨?_,rfl⟩
    intro i
    by_cases hi : i = j
    · subst i
      simpa [replace] using (rootCenter_rv A R j hcover hR p hp.1).symm
    · simp [replace,hi]
  locus_definable := setDefinable A
  center_graph := by
    let F := Map.comp (rootVFCoordinateMap S j) (rootSelectionMap A R j hcover hR)
    have hval (a : A) : (F a).val (0 : Fin 1) = rootCenter A R j hcover hR a.val := by
      change (rootSelectionMap A R j hcover hR a).val j = _
      simp only [rootCenter,dif_pos a.property]
    apply RelationDefinable.congr _ _ (Map.graph_definable F)
    intro p z
    constructor
    · rintro ⟨a,rfl,rfl⟩
      exact ⟨⟨a.property,a.property⟩,hval a⟩
    · rintro ⟨hp,hz⟩
      refine ⟨⟨p,hp.1⟩,rfl,?_⟩
      funext i
      fin_cases i
      exact (hval ⟨p,hp.1⟩).trans hz.symm

@[simp] theorem rootFocus_locus (hA : IsRVPullback (carrier A))
    (htag : Tagged (carrier A) j k) :
    (rootFocus A R j k hcover hR hA htag).locus = carrier A := rfl

@[simp] theorem rootFocus_center_apply (hA : IsRVPullback (carrier A))
    (htag : Tagged (carrier A) j k) (a : A) :
    (rootFocus A R j k hcover hR hA htag).center a.val =
      (rootSelectionMap A R j hcover hR a).val j := by
  simp only [rootFocus,rootCenter,dif_pos a.property]

end IntegrationInACVF.Section6
