import IntegrationSection6.ElementaryBlowup
import Section4.RVIsoTools

/-! The canonical RV keys of an elementary blowup: new volume coordinates
followed by all old domain labels. This is the definable isomorphism in6.9. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {k n r : ℕ}

def selectRVTuple (ρ : Fin r → Fin n) (A : DefSet (rawRVSpace (M := M) n) S) :
    Map A (DefSet.univ (rawRVSpace r) S) := by
  have hcode (c : (rawRVSpace (M := M) n).domain) :
      rvValues ((rawRVSpace n).decode c ∘ ρ) = c.val ∘ ρ :=
    funext (fun i => congrFun (rvValues_decode c) (ρ i))
  exact Map.ofCodes A (fun a => a ∘ ρ) (fun z => z ∘ ρ)
    (fun _ => Set.DefinableFun.proj LRV)
    (fun c => ⟨_,hcode c⟩) (fun c => rvValues_injective
      ((rvValues_decode _).trans (hcode c).symm))

def elementaryKeyMap (U : RVObject (M := M) S k) (i : Fin k) :
    Map (elementary U i).domain (DefSet.univ (rawRVSpace (k+U.arity)) S) :=
  (rvPack (DefSet.univ (rawRVSpace k) S) U.domain).comp
    (Map.pair (elementary U i).volume (elementaryProjection U i))

@[simp] theorem elementaryKeyMap_value (U : RVObject (M := M) S k) (i : Fin k)
    (a : (elementary U i).domain) :
    (elementaryKeyMap U i a).val = rvAppend ((elementary U i).value a)
      (elementaryProjection U i a).val := rfl

theorem elementaryKeyMap_injective (U : RVObject (M := M) S k) (i : Fin k)
    (h : Admissible U i) : Function.Injective (elementaryKeyMap U i) := by
  intro a b hab
  have hkey := rvAppend_injective (congrArg Subtype.val hab)
  have hproj : elementaryProjection U i a = elementaryProjection U i b :=
    Subtype.ext (congrArg Prod.snd hkey)
  have hvol := congrArg (fun p => p.1 i) hkey
  change (elementary U i).value a i = (elementary U i).value b i at hvol
  rw [elementary_value,elementary_value,blowupValue_same,blowupValue_same,hproj] at hvol
  have hnz : U.value (elementaryProjection U i b) i ≠ 0 := by
    intro he
    exact h.nonzero _ ((congrArg Subtype.val he).trans RVOperations.zero_val)
  have hpar : elementaryParameter U i a = elementaryParameter U i b := by
    apply Subtype.ext
    funext j
    fin_cases j
    exact mul_right_cancel₀ hnz hvol
  have hunpack : rvUnpack U.domain (positiveRV S) a = rvUnpack U.domain (positiveRV S) b := by
    apply Subtype.ext
    exact Prod.ext (congrArg Subtype.val hproj) (congrArg Subtype.val hpar)
  have he := congrArg (rvPack U.domain (positiveRV S)).toImage hunpack
  simpa only [rvPack_unpack] using he

def elementaryKeyObject (U : RVObject (M := M) S k) (i : Fin k) : RVObject (M := M) S k where
  arity := k+U.arity
  domain := (elementaryKeyMap U i).image
  volume := selectRVTuple (Fin.castAdd U.arity) (elementaryKeyMap U i).image

def elementaryKeyIso (U : RVObject (M := M) S k) (i : Fin k) (h : Admissible U i) :
    elementary U i ≅ elementaryKeyObject U i := by
  apply rvIsoOfVolumePreservingBijection (elementaryKeyMap U i).toImage
  · constructor
    · intro a b he
      apply elementaryKeyMap_injective U i h
      apply Subtype.ext
      exact congrArg (fun x : (elementaryKeyMap U i).image => x.val) he
    · rintro ⟨b,a,ha⟩
      exact ⟨a,Subtype.ext ha⟩
  · intro a
    funext j
    change rvAppend ((elementary U i).value a)
      (elementaryProjection U i a).val (Fin.castAdd U.arity j) = _
    exact Fin.append_left _ _ j

end IntegrationInACVF.Section6
