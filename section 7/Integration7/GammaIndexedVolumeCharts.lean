module

public import Integration7.GammaVolumePresentationGeometry
public import Integration7.GammaVolumeParameterGeometry
public import Integration7.IndexedVolumeChartTransfer

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Indexed volume comparisons retain their original-Gamma chart,
independently of the auxiliary exception parameters used for realization. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV Point GammaGraphDefinable gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem GammaRVVolumeSchema.indexedRowIso_gamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F G : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (hEq : ∀ t ∈ T, F.sameRow G (rvValues t))
    (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M)) :
    (F.indexedRowIso hc C G BP hEq P Q hP hQ).GammaDefinable B :=
  gamma_volume_iso_of_label_identity hc _ (P.gamma_object hc C hP) rfl (fun _ => rfl)

theorem GammaRVVolumeIsoCertificateSchema.indexedRealizeGamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (H : GammaRVVolumeIsoCertificateSchema B p a b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (hvalid : ∀ t ∈ T, H.valid (rvValues t))
    (P : H.source.IndexedPresentation BP) (Q : H.target.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hBP : BP.codes ⊆ (C.base : Set M)) (hB : B.real ⊆ (C.base : Set M)) :
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      ∃ f : RVVolumeIso ((P.inContext hc C hP).toObject.extend hCD)
        ((Q.inContext hc C hQ).toObject.extend hCD), f.GammaDefinable B := by
  obtain ⟨D,hCD,f,hf⟩ := H.indexedRealize hc C BP hvalid P Q hP hQ hBP hB
  have hSource := gamma_essential_volume_domain _ ((P.gamma_object hc C hP).extend hCD).coordinates
  have hTarget := gamma_essential_volume_domain _ ((Q.gamma_object hc C hQ).extend hCD).coordinates
  let L := gammaLogicInput B
  have hR := L.restrict_graph hSource (L.swap_graph
    (L.restrict_graph hTarget (L.swap_graph (indexedVolumeChartRelation_gammaGraph H))))
  refine ⟨D,hCD,f,?_⟩
  apply GammaGraphDefinable.congr hR
  intro p q
  constructor
  · rintro ⟨hp,hq,hRel⟩
    let u := (⟨p.2,hp⟩ : ((P.inContext hc C hP).toObject.extend hCD).essential.obj.domain)
    let v := (⟨q.2,hq⟩ : ((Q.inContext hc C hQ).toObject.extend hCD).essential.obj.domain)
    exact ⟨u,rfl,congrArg Subtype.val ((hf u v).mp hRel)⟩
  · rintro ⟨u,hu,hq⟩
    refine ⟨(congrArg (fun r => r ∈ _) hu).mp u.property,
      (congrArg (fun r => r ∈ _) hq).mp (finiteIsoMap f.iso u).property,?_⟩
    change indexedVolumeChartRelation H p.2 q.2
    rw [← hu,← hq]
    exact (hf u (finiteIsoMap f.iso u)).mpr rfl

end IntegrationInACVF.Section7
