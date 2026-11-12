import IntegrationSection6.ElementaryIsomorphism
import IntegrationSection6.Subobjects
import IntegrationSection6.Iteration

/-!
# General blowups and the common-blowup relation

Definition 6.1 retains an actual definable locus, an RV isomorphism from
its chosen elementary presentation, and the unchanged complementary object.
Finite iteration is forward only. Definition 6.7 uses isomorphic forward
blowups, without assuming equivalence or the kernel theorem.
-/

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace IntegrationInACVF.Section6

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ}

/-- Definition 6.1 with the full locus and presentation data. -/
structure Blowup (U V : RVObject (M := M) S k) where
  center : RVObject (M := M) S k
  coordinate : Fin k
  admissible : Admissible center coordinate
  locus : DefSet (rawRVSpace (M := M) U.arity) S
  contained : locus.carrier ⊆ U.domain.carrier
  chart : center ≅ U.restrict locus contained
  result : V ≅ rvCoprodObject (elementary center coordinate)
    (U.restrict (complement U locus) (complement_subset U locus))

namespace Blowup

variable {U V W U' V' : RVObject (M := M) S k}

/-- Changing the real tuple presentation of the result. -/
def targetIso (h : Blowup U V) (e : V' ≅ V) : Blowup U V' :=
  { h with result := e.trans h.result }

/-- Transport of the actual locus through an arbitrary RV isomorphism. -/
def sourceIso (h : Blowup U V) (e : U' ≅ U) : Blowup U' V where
  center := h.center
  coordinate := h.coordinate
  admissible := h.admissible
  locus := subobjectImage e.symm h.locus h.contained
  contained := subobjectImage_subset e.symm h.locus h.contained
  chart := h.chart.trans (subobjectImageIso e.symm h.locus h.contained)
  result := h.result.trans (rvCoprodIso (Iso.refl _)
    (complementImageIso e.symm h.locus h.contained))

/-- Corollary 6.4: corresponding actual loci yield isomorphic blowups. -/
theorem corollary_6_4 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (h : Blowup U U') (g : Blowup V V') (e : U ≅ V)
    (hlocus : (subobjectImage e h.locus h.contained).carrier = g.locus.carrier) :
    Nonempty (U' ≅ V') := by
  let ec : h.center ≅ g.center := h.chart.trans
    ((subobjectImageIso e h.locus h.contained).trans
      ((rvIsoOfCarrierEq _ _ _ _ hlocus (fun _ => rfl)).trans g.chart.symm))
  let er : U.restrict (complement U h.locus) (complement_subset U h.locus) ≅
      V.restrict (complement V g.locus) (complement_subset V g.locus) :=
    (complementImageIso e h.locus h.contained).trans
    (rvIsoOfCarrierEq _ _ _ _ (by
      change V.domain.carrier \ (subobjectImage e h.locus h.contained).carrier =
        V.domain.carrier \ g.locus.carrier
      rw [hlocus]) (fun _ => rfl))
  exact ⟨h.result.trans ((rvCoprodIso
    (elementaryIso hκ hs hsmall h.coordinate g.coordinate h.admissible g.admissible ec)
    er).trans g.result.symm)⟩

end Blowup

/-- Exactly n general blowups, permitting isomorphic tuple presentations
at length zero. This does not insert backward blowup steps. -/
inductive IteratedBlowup : ℕ → RVObject (M := M) S k → RVObject (M := M) S k → Prop
  | zero {U V} : Nonempty (U ≅ V) → IteratedBlowup 0 U V
  | cons {n U V W} : Blowup U V → IteratedBlowup n V W → IteratedBlowup (n + 1) U W

namespace IteratedBlowup

variable {U V W U' V' : RVObject (M := M) S k} {m n : ℕ}

theorem refl (U : RVObject (M := M) S k) : IteratedBlowup 0 U U := .zero ⟨Iso.refl U⟩

theorem sourceIso (h : IteratedBlowup n U V) (e : U' ≅ U) : IteratedBlowup n U' V := by
  cases h with
  | zero he => exact .zero (he.map e.trans)
  | cons h ht => exact .cons (h.sourceIso e) ht

theorem targetIso (h : IteratedBlowup n U V) (e : V ≅ V') : IteratedBlowup n U V' := by
  induction h with
  | zero he => exact .zero (he.map (fun f => f.trans e))
  | cons h _ ih => exact .cons h (ih e)

theorem single (h : Blowup U V) : IteratedBlowup 1 U V := .cons h (.refl V)

theorem trans (h : IteratedBlowup m U V) (g : IteratedBlowup n V W) :
    IteratedBlowup (m + n) U W := by
  induction h with
  | zero he =>
    obtain ⟨e⟩ := he
    simpa using g.sourceIso e
  | cons h _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      IteratedBlowup.cons h (ih g)

end IteratedBlowup

/-- Definition 6.7: isomorphic forward finite blowups, over the fixed base. -/
def Isp (U V : RVObject (M := M) S k) : Prop :=
  ∃ m n U' V', IteratedBlowup m U U' ∧ IteratedBlowup n V V' ∧ Nonempty (U' ≅ V')

namespace Isp

variable {U V U' V' : RVObject (M := M) S k}

theorem refl (U : RVObject (M := M) S k) : Isp U U :=
  ⟨0, 0, U, U, .refl U, .refl U, ⟨Iso.refl U⟩⟩

theorem symm (h : Isp U V) : Isp V U := by
  obtain ⟨m, n, A, B, hu, hv, ⟨e⟩⟩ := h
  exact ⟨n, m, B, A, hv, hu, ⟨e.symm⟩⟩

theorem of_iso (e : U ≅ V) : Isp U V :=
  ⟨0, 0, U, V, .refl U, .refl V, ⟨e⟩⟩

/-- Corollary 6.6 on the actual forward-blowup definition. -/
theorem corollary_6_6 (h : Isp U V) (e : U' ≅ U) (f : V' ≅ V) : Isp U' V' := by
  obtain ⟨m, n, A, B, hu, hv, he⟩ := h
  exact ⟨m, n, A, B, hu.sourceIso e, hv.sourceIso f, he⟩

theorem of_iterated {n : ℕ} (h : IteratedBlowup n U V) : Isp U V :=
  ⟨n, 0, V, V, h, .refl V, ⟨Iso.refl V⟩⟩

end Isp

end IntegrationInACVF.Section6
