import Integration7.IndexedVolumeCoproductValues
import Integration7.GammaVolumeRelabelRealization

/-! Indexed assembly commutes with actual volume coproducts. The
comparison retains all coordinates and the density, in a finite context. -/

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
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem GammaRVVolumeSchema.indexedCoprodRealize
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (G : GammaRVVolumeSchema B p b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.object.finiteRow (rvValues t)) (hG : ∀ t ∈ T, G.object.finiteRow (rvValues t))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (Z : (F.coprodFormula G).IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hZ : Z.finite.codes ⊆ (C.base : Set M)) (hB : B.real ⊆ (C.base : Set M)) :
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      Nonempty (RVVolumeIso ((Z.inContext hc C hZ).toObject.extend hCD)
        (((P.inContext hc C hP).toObject.coprod (Q.inContext hc C hQ).toObject).extend hCD)) :=
  gammaVolumeRelabelRealize hc C (indexedVolumeCoprodEquiv hc C F G BP P Q Z hP hQ hZ)
    (indexedVolumeCoprodEquiv_gammaGraph hc C F G BP P Q Z hP hQ hZ)
    (fun u => (indexedVolumeCoprodEquiv_values hc C F G BP hF hG P Q Z hP hQ hZ u).1)
    (fun u => (indexedVolumeCoprodEquiv_values hc C F G BP hF hG P Q Z hP hQ hZ u).2) hB

end IntegrationInACVF.Section7
