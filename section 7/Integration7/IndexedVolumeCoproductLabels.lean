import Integration7.IndexedVolumeRowSemantics
import Integration7.GammaVolumeCoproductFormulas
import Integration7.NormalizedRVTags
import Integration7.VolumeCoproduct
import IntegrationSection6.GammaIndexedCoproductGraphs

/-! The actual indexed coproduct labels distribute the index tuple
through the two tags. The complete graph remains original-Gamma definable. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV Point GammaGraphDefinable)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def indexedVolumeCoprodSourceEquiv
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (G : GammaRVVolumeSchema B p b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (Z : (F.coprodFormula G).IndexedPresentation BP) (hZ : Z.finite.codes ⊆ (C.base : Set M)) :
    (Z.inContext hc C hZ).underlying.obj.domain ≃
      indexedDomain T (fun t => graphCoprodDomain
        (F.object.rowDomain (rvValues t)) (G.object.rowDomain (rvValues t))) :=
  Equiv.subtypeEquivRight (fun w =>
    (Set.ext_iff.mp (GammaVolumeGraphPresentation.inContext_domain hc C Z hZ) w).trans
      (and_congr Iff.rfl (F.object.coprod_row_domain_formula G.object _
        (fun i => (indexedLeft w i).property) (indexedRight w))))

def indexedVolumeCoprodTargetEquiv
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (G : GammaRVVolumeSchema B p b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M)) :
    ((P.inContext hc C hP).toObject.coprod (Q.inContext hc C hQ).toObject).underlying.obj.domain ≃
      graphCoprodDomain (indexedDomain T (fun t => F.object.rowDomain (rvValues t)))
        (indexedDomain T (fun t => G.object.rowDomain (rvValues t))) := by
  apply Equiv.subtypeEquivRight
  intro w
  constructor
  · rintro (⟨u,hu⟩ | ⟨v,hv⟩)
    · exact Or.inl ⟨u.val,(Set.ext_iff.mp (GammaVolumeGraphPresentation.inContext_domain hc C P hP) _).mp
        u.property,(rvLeftTag_normalize u.val).trans hu⟩
    · exact Or.inr ⟨v.val,(Set.ext_iff.mp (GammaVolumeGraphPresentation.inContext_domain hc C Q hQ) _).mp
        v.property,(rvRightTag_normalize v.val).trans hv⟩
  · rintro (⟨x,hx,hw⟩ | ⟨y,hy,hw⟩)
    · exact Or.inl ⟨⟨x,(Set.ext_iff.mp (GammaVolumeGraphPresentation.inContext_domain hc C P hP) _).mpr hx⟩,
        (rvLeftTag_normalize x).symm.trans hw⟩
    · exact Or.inr ⟨⟨y,(Set.ext_iff.mp (GammaVolumeGraphPresentation.inContext_domain hc C Q hQ) _).mpr hy⟩,
        (rvRightTag_normalize y).symm.trans hw⟩

def indexedVolumeCoprodEquiv
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (G : GammaRVVolumeSchema B p b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (Z : (F.coprodFormula G).IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hZ : Z.finite.codes ⊆ (C.base : Set M)) :
    (Z.inContext hc C hZ).underlying.obj.domain ≃
      ((P.inContext hc C hP).toObject.coprod (Q.inContext hc C hQ).toObject).underlying.obj.domain :=
  (indexedVolumeCoprodSourceEquiv hc C F G BP Z hZ).trans
    ((indexedCoprodEquiv T (fun t => F.object.rowDomain (rvValues t))
      (fun t => G.object.rowDomain (rvValues t))).trans
        (indexedVolumeCoprodTargetEquiv hc C F G BP P Q hP hQ).symm)

theorem indexedVolumeCoprodEquiv_gammaGraph
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (G : GammaRVVolumeSchema B p b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (Z : (F.coprodFormula G).IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hZ : Z.finite.codes ⊆ (C.base : Set M)) :
    GammaGraphDefinable B (fun (w : Point (M := M) 0 (p+(1+(a+b))))
      (y : Point (M := M) 0 (1+((p+a)+(p+b)))) =>
        ∃ u : (Z.inContext hc C hZ).underlying.obj.domain, u.val = w.2 ∧
          (indexedVolumeCoprodEquiv hc C F G BP P Q Z hP hQ hZ u).val = y.2) := by
  apply GammaGraphDefinable.congr
    (gamma_indexed_coprod_equiv_graph T (fun t => F.object.rowDomain (rvValues t))
      (fun t => G.object.rowDomain (rvValues t)) (F.object.indexed_domain_graph BP)
        (G.object.indexed_domain_graph BP))
  intro w y
  constructor
  · rintro ⟨u,hu,hy⟩
    exact ⟨(indexedVolumeCoprodSourceEquiv hc C F G BP Z hZ).symm u,hu,hy⟩
  · rintro ⟨u,hu,hy⟩
    exact ⟨indexedVolumeCoprodSourceEquiv hc C F G BP Z hZ u,hu,hy⟩

end IntegrationInACVF.Section7
