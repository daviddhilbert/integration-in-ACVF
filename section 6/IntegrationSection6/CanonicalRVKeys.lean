import IntegrationSection6.ElementaryKeys

/-! Canonical RV labeling retains the old domain tuple and appends its
volume tuple. It is an actual volume-preserving RV isomorphism, without
saturation or a smallness assumption on the real presentation code set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}

def canonicalRVKeyMap (U : RVObject (M := M) S n) :
    Map U.domain (DefSet.univ (rawRVSpace (n+U.arity)) S) :=
  (rvPack (DefSet.univ (rawRVSpace n) S) U.domain).comp
    (Map.pair U.volume (Map.id U.domain))

@[simp] theorem canonicalRVKeyMap_value (U : RVObject (M := M) S n) (u : U.domain) :
    (canonicalRVKeyMap U u).val = rvAppend (U.value u) u.val := rfl

theorem canonicalRVKeyMap_injective (U : RVObject (M := M) S n) :
    Function.Injective (canonicalRVKeyMap U) := by
  intro a b he
  have hk := rvAppend_injective (congrArg Subtype.val he)
  exact Subtype.ext (congrArg Prod.snd hk)

def canonicalRVKeyObject (U : RVObject (M := M) S n) : RVObject (M := M) S n where
  arity := n+U.arity
  domain := (canonicalRVKeyMap U).image
  volume := selectRVTuple (Fin.castAdd U.arity) (canonicalRVKeyMap U).image

def canonicalRVKeyIso (U : RVObject (M := M) S n) : U ≅ canonicalRVKeyObject U := by
  apply rvIsoOfVolumePreservingBijection (canonicalRVKeyMap U).toImage
  · constructor
    · intro a b he
      apply canonicalRVKeyMap_injective U
      apply Subtype.ext
      exact congrArg (fun x : (canonicalRVKeyMap U).image => x.val) he
    · rintro ⟨b,a,ha⟩
      exact ⟨a,Subtype.ext ha⟩
  · intro a
    funext j
    change rvAppend (U.value a) a.val (Fin.castAdd U.arity j) = _
    exact Fin.append_left _ _ j

theorem canonicalRVKeyIso_volume (U : RVObject (M := M) S n) (a : U.domain) :
    (canonicalRVKeyObject U).value ((canonicalRVKeyIso U).hom.map a) = U.value a := by
  funext j
  change rvAppend (U.value a) a.val (Fin.castAdd U.arity j) = _
  exact Fin.append_left _ _ j

/-- Algebraicity is unchanged by this volume-preserving reparametrization. -/
theorem canonicalRVKey_admissible (U : RVObject (M := M) S n) (i : Fin n)
    (h : Admissible U i) : Admissible (canonicalRVKeyObject U) i := by
  constructor
  · rintro ⟨b,a,rfl⟩
    change ((canonicalRVKeyObject U).value ((canonicalRVKeyIso U).hom.map a) i).val ≠ _
    rw [canonicalRVKeyIso_volume]
    exact h.nonzero a
  · rintro ⟨b,a,rfl⟩
    have ha := h.algebraic a
    rw [← canonicalRVKeyIso_volume U a] at ha
    exact ha

end IntegrationInACVF.Section6
