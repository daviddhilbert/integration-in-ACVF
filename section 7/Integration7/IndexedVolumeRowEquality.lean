import Integration7.GammaVolumeIndexedPresentations
import Integration7.GammaVolumePresentationRowIsomorphisms
import IntegrationSection6.GammaSchemaIndexedEquality

/-! Full equality of volume-schema rows gives the actual joint
volume isomorphism, by identity on labels and equality of both graphs. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

def GammaRVVolumeSchema.indexedRowIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F G : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hEq : ∀ t ∈ T, F.sameRow G (rvValues t))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M)) :
    RVVolumeIso (P.inContext hc C hP).toObject (Q.inContext hc C hQ).toObject := by
  have hD : indexedDomain T (fun t => F.object.rowDomain (rvValues t)) =
      indexedDomain T (fun t => G.object.rowDomain (rvValues t)) := by
    ext w
    constructor
    · rintro ⟨ht,hx⟩
      exact ⟨ht,((hEq _ ht).1.2.1 (rvValues (indexedRight w))).mp hx⟩
    · rintro ⟨ht,hx⟩
      exact ⟨ht,((hEq _ ht).1.2.1 (rvValues (indexedRight w))).mpr hx⟩
  have hR : ∀ w y,
      (w ∈ indexedDomain T (fun t => F.object.rowDomain (rvValues t)) ∧
        indexedVolume BP.totalVolume (fun t => F.object.rowValue (rvValues t)) w = y) ↔
      (w ∈ indexedDomain T (fun t => G.object.rowDomain (rvValues t)) ∧
        indexedVolume BP.totalVolume (fun t => G.object.rowValue (rvValues t)) w = y) := by
    intro w y
    by_cases ht : indexedLeft w ∈ T
    · have hValue := F.object.rowValue_eq_of_sameRow G.object _ (hEq _ ht).1
      have hV : indexedVolume BP.totalVolume (fun t => F.object.rowValue (rvValues t)) w =
          indexedVolume BP.totalVolume (fun t => G.object.rowValue (rvValues t)) w :=
        congrArg (fun v => Fin.append (BP.totalVolume (indexedLeft w)) v)
          (congrFun hValue (indexedRight w))
      rw [hD,hV]
    · exact ⟨fun h => False.elim (ht h.1.1),fun h => False.elim (ht h.1.1)⟩
  have hW : ∀ w ω, F.indexedDensity T w ω ↔ G.indexedDensity T w ω := by
    intro w ω
    change (_ ∧ _) ↔ (_ ∧ _)
    by_cases ht : indexedLeft w ∈ T
    · exact and_congr (Iff.of_eq (congrArg (fun D => w ∈ D) hD))
        ((hEq _ ht).2.2.2 (rvValues (indexedRight w)) (rvValues ω))
    · exact ⟨fun h => False.elim (ht h.1.1),fun h => False.elim (ht h.1.1)⟩
  exact gammaVolumePresentationIsoOfRelations hc C P Q hD hR hW hP hQ

end IntegrationInACVF.Section7
