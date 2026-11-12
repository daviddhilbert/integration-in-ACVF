import IntegrationSection6.FocusLabelAlgebraicity
import IntegrationSection6.FocusFibres
import IntegrationSection6.ElementaryKeys
import Section4.CanonicalLift

/-! Semantic canonical-lift presentations and the algebraicity consequence
of a full nonzero focus, on the actual released VF/RV carriers. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}

/-- The literal carrier condition of the canonical lift. This is a
presentation interface, not a bijection or kernel assumption. -/
def PresentsLift (U : RVObject (M := M) S n)
    (A : SpecialTransformations.Section5.DefSet (M := M) S n U.arity) : Prop :=
  ∀ p, p ∈ carrier A ↔ ∃ u : U.domain, u.val = p.2 ∧ U.value u = fun i => rv (p.1 i)

theorem PresentsLift.pullback {U : RVObject (M := M) S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n U.arity}
    (h : PresentsLift U A) : IsRVPullback (carrier A) := by
  apply (isRVPullback_iff _).mpr
  intro p hp q he
  obtain ⟨hv,hl⟩ := (sameRV_iff _ _).mp he
  obtain ⟨u,hu,hvol⟩ := (h p).mp hp
  exact (h q).mpr ⟨u,hu.trans hl,hvol.trans (funext hv)⟩

theorem PresentsLift.representative {U : RVObject (M := M) S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n U.arity}
    (h : PresentsLift U A) (u : U.domain) :
    ∃ p : A, p.val.2 = u.val ∧ (fun i => rv (p.val.1 i)) = U.value u := by
  obtain ⟨x,hx⟩ := tupleRV_surjective (U.value u)
  let p : Point (M := M) n U.arity := (x,u.val)
  refine ⟨⟨p,(h p).mpr ⟨u,rfl,hx.symm⟩⟩,rfl,hx⟩

/-- The dependence part of6.9, in the exact original small parameter base.
The nonzero condition is that of normalized paper focus loci. -/
theorem admissible_of_fullFocus {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {U : RVObject (M := M) S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n U.arity}
    (h : PresentsLift U A) {j : Fin n} {k : Fin U.arity}
    (D : Focus A j k) (hfull : carrier A ⊆ D.locus)
    (hnz : ∀ p ∈ carrier A, p.1 j ≠ (0 : VF (M := M))) : Admissible U j where
  nonzero u := by
    obtain ⟨p,_,hp⟩ := h.representative u
    intro hz
    have he : CanonicalRV.encodedRv (p.val.1 j) = 0 := by
      apply Subtype.ext
      exact (congrArg Subtype.val (congrFun hp j)).trans (hz.trans RVOperations.zero_val.symm)
    exact (RVOperations.rv_ne_zero _).mpr (hnz p.val p.property) he
  algebraic u := by
    obtain ⟨p,_,hp⟩ := h.representative u
    have ha := fullFocus_label_algebraic hκ hs hsmall D h.pullback hfull p
    change AlgebraicAt (coordinateBase S j (fun i => rv (p.val.1 i))) .rv
      ((fun i => rv (p.val.1 i)) j).val at ha
    rw [hp] at ha
    exact ha

end IntegrationInACVF.Section6
