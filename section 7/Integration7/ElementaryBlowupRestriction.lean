import Integration7.ElementaryBlowupConstruction
import Integration7.DefinableMapPreimages

/-! Restrict a concrete elementary blowup to the preimage of an actual
definable source locus. Both the chart and density restrict. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem BlowupAdmissible.restrict {U : PositiveRVVolumeObject (M := M) S k}
    (h : BlowupAdmissible U)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier) : BlowupAdmissible (U.restrict A hA) where
  nonzero u := h.nonzero ⟨u.val, hA u.property⟩
  algebraic u := h.algebraic ⟨u.val, hA u.property⟩

namespace ElementaryBlowup

variable {U W : PositiveRVVolumeObject (M := M) S k} (b : ElementaryBlowup U W)
variable (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
variable (hA : A.carrier ⊆ U.underlying.obj.domain.carrier)

def sourcePreimage : DefSet (rawRVSpace (M := M) W.underlying.obj.arity) S :=
  definableMapPreimage b.projection A

theorem sourcePreimage_subset : (b.sourcePreimage A).carrier ⊆ W.underlying.obj.domain.carrier :=
  definableMapPreimage_subset b.projection A

theorem mem_sourcePreimage (w : W.underlying.obj.domain) :
    w.val ∈ (b.sourcePreimage A).carrier ↔ (b.projection w).val ∈ A.carrier :=
  mem_definableMapPreimage b.projection A w

def restrictedChart : Map (b.sourcePreimage A) (A.prod (blowupConeSet S)) :=
  (b.chartMap.restrict (b.sourcePreimage_subset A)).corestrict (by
    intro w
    refine ⟨?_, (b.chartMap ⟨w.val, b.sourcePreimage_subset A w.property⟩).property.2⟩
    exact (b.mem_sourcePreimage A ⟨w.val, b.sourcePreimage_subset A w.property⟩).mp w.property)

include hA in
theorem restrictedChart_bijective : Function.Bijective (b.restrictedChart A) := by
  constructor
  · intro w z he
    have h : b.chartMap ⟨w.val, b.sourcePreimage_subset A w.property⟩ =
        b.chartMap ⟨z.val, b.sourcePreimage_subset A z.property⟩ :=
      Subtype.ext (congrArg (fun p : A.prod (blowupConeSet S) => p.val) he)
    exact Subtype.ext (congrArg (fun p : W.underlying.obj.domain => p.val) (b.chartMap_bijective.1 h))
  · intro p
    let p' : U.underlying.obj.domain.prod (blowupConeSet S) :=
      ⟨p.val, hA p.property.1, p.property.2⟩
    obtain ⟨w, hw⟩ := b.chartMap_bijective.2 p'
    have hmem : w.val ∈ (b.sourcePreimage A).carrier := by
      apply (b.mem_sourcePreimage A w).mpr
      have hp : (b.projection w).val = p.val.1 :=
        congrArg (fun q : U.underlying.obj.domain.prod (blowupConeSet S) => q.val.1) hw
      rw [hp]
      exact p.property.1
    exact ⟨⟨w.val, hmem⟩, Subtype.ext
      (congrArg (fun q : U.underlying.obj.domain.prod (blowupConeSet S) => q.val) hw)⟩

def restrict : ElementaryBlowup (U.restrict A hA)
    (W.restrict (b.sourcePreimage A) (b.sourcePreimage_subset A)) where
  admissible := b.admissible.restrict A hA
  chartMap := b.restrictedChart A
  chartMap_bijective := b.restrictedChart_bijective A hA
  head w i := b.head ⟨w.val, b.sourcePreimage_subset A w.property⟩ i
  last w := b.last ⟨w.val, b.sourcePreimage_subset A w.property⟩
  volume w := b.volume ⟨w.val, b.sourcePreimage_subset A w.property⟩

end ElementaryBlowup
end IntegrationInACVF.Section7
