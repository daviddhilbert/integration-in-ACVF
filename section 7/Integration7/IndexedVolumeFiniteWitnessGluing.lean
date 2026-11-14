import Integration7.IndexedVolumeCommonRealization
import Integration7.IndexedVolumeBinaryPartitions
import Integration7.IndexedVolumeEmpty
import Integration7.VolumeBlowupAddition

/-! A finite definable cover by common-forward-volume-blowup witnesses
glues over any actual finite-volume RV index base. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV Point GammaSetDefinable gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}

theorem finiteVolumePresentationContainingContext {a n : ℕ}
    {T : Set (Fin a → RV (M := M))}
    {R : (Fin a → RV (M := M)) → (Fin n → RV (M := M)) → Prop}
    (C : BaseContext M) (P : GammaFiniteGraphPresentation B a n T R)
    (hB : B.real ⊆ (C.base : Set M)) :
    ∃ D : BaseContext M, (C.base : Set M) ⊆ (D.base : Set M) ∧ P.codes ⊆ (D.base : Set M) := by
  obtain ⟨E,hE,hCodes⟩ := P.finite_extra
  refine ⟨finiteVolumeParameterContext C E hE,
    (fun _ hx => finiteVolumeParameterContext_contains C E hE (Or.inl hx)),?_⟩
  rw [hCodes]
  rintro x (hx | hx)
  · exact finiteVolumeParameterContext_contains C E hE (Or.inl (hB hx))
  · exact finiteVolumeParameterContext_contains C E hE (Or.inr hx)

theorem gamma_volume_common_finite_indexed_glue
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (G : GammaRVVolumeSchema B p b k (fun _ => .rv))
    (J : Finset (GammaVolumeCommonSchema F G)) :
    ∀ (C : BaseContext M) {T : Set (Fin p → RV (M := M))}
      {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
      (BP : GammaFiniteGraphPresentation B p d T R),
      (∀ t ∈ T, F.valid (rvValues t)) → (∀ t ∈ T, G.valid (rvValues t)) →
      (∀ t ∈ T, ∃ W ∈ J, W.valid (rvValues t)) →
      ∀ (P : F.IndexedPresentation BP) (Q : G.IndexedPresentation BP)
        (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M)),
        BP.codes ⊆ (C.base : Set M) → B.real ⊆ (C.base : Set M) →
        ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
          VolumeBlowupEquivalent ((P.inContext hc C hP).toObject.extend hCD)
            ((Q.inContext hc C hQ).toObject.extend hCD) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    intro C T R BP hF hG hCover P Q hP hQ hBP hB
    have hEmpty : T = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro t ht
      obtain ⟨W,hW,_⟩ := hCover t ht
      exact Finset.notMem_empty W hW
    exact ⟨C,Set.Subset.refl _,VolumeBlowupEquivalent.of_iso C
      (indexedVolumeEmptyIso hc C F G BP hEmpty P Q hP hQ)⟩
  | @insert W J hNot ih =>
    intro C T R BP hF hG hCover P Q hP hQ hBP hB
    let E : Set (Fin p → RV (M := M)) := {t | t ∈ T ∧ W.valid (rvValues t)}
    have hET : E ⊆ T := fun _ h => h.1
    have hWΓ : GammaSetDefinable B {t : Point (M := M) 0 p | W.valid (rvValues t.2)} :=
      gamma_rv_set_from_tuple_formula (W.valid_definable hc)
    have hEΓ : GammaSetDefinable B {t : Point (M := M) 0 p | t.2 ∈ E} :=
      (gammaLogicInput B).inter BP.domain_graph hWΓ
    let BPA := BP.restrictDomain E hET hEΓ
    let BPC := BP.restrictDomain (T \ E) (fun _ h => h.1) ((gammaLogicInput B).sdiff BP.domain_graph hEΓ)
    let PA := F.indexedVolumePresentation BPA (fun t ht => hF t ht.1)
    let QA := G.indexedVolumePresentation BPA (fun t ht => hG t ht.1)
    let PC := F.indexedVolumePresentation BPC (fun t ht => hF t ht.1)
    let QC := G.indexedVolumePresentation BPC (fun t ht => hG t ht.1)
    obtain ⟨C₁,hCC₁,hBPA₁⟩ := finiteVolumePresentationContainingContext C BPA hB
    obtain ⟨C₂,hC₁C₂,hBPC₂⟩ := finiteVolumePresentationContainingContext C₁ BPC (hB.trans hCC₁)
    obtain ⟨C₃,hC₂C₃,hPA₃⟩ := PA.exists_containingContext C₂ (hB.trans (hCC₁.trans hC₁C₂))
    obtain ⟨C₄,hC₃C₄,hQA₄⟩ := QA.exists_containingContext C₃ (hB.trans (hCC₁.trans (hC₁C₂.trans hC₂C₃)))
    obtain ⟨C₅,hC₄C₅,hPC₅⟩ := PC.exists_containingContext C₄
      (hB.trans (hCC₁.trans (hC₁C₂.trans (hC₂C₃.trans hC₃C₄))))
    obtain ⟨D₀,hC₅D₀,hQC⟩ := QC.exists_containingContext C₅
      (hB.trans (hCC₁.trans (hC₁C₂.trans (hC₂C₃.trans (hC₃C₄.trans hC₄C₅)))))
    let hCC₂ := hCC₁.trans hC₁C₂
    let hC₂D₀ := hC₂C₃.trans (hC₃C₄.trans (hC₄C₅.trans hC₅D₀))
    let hCD₀ := hCC₂.trans hC₂D₀
    let hPA := hPA₃.trans (hC₃C₄.trans (hC₄C₅.trans hC₅D₀))
    let hQA := hQA₄.trans (hC₄C₅.trans hC₅D₀)
    let hPC := hPC₅.trans hC₅D₀
    let hBPA := hBPA₁.trans (hC₁C₂.trans hC₂D₀)
    let hBPC := hBPC₂.trans hC₂D₀
    obtain ⟨D₁,hD₀D₁,L,R,hL,hR,e⟩ := W.indexedRealize hc D₀ BPA (fun t ht => ht.2)
      PA QA hPA hQA hBPA (hB.trans hCD₀)
    have hInside : VolumeBlowupEquivalent
        ((PA.inContext hc D₀ hPA).toObject.extend hD₀D₁)
        ((QA.inContext hc D₀ hQA).toObject.extend hD₀D₁) :=
      ⟨W.leftLength,W.rightLength,L,R,hL,hR,e⟩
    have hCoverC : ∀ t ∈ T \ E, ∃ W ∈ J, W.valid (rvValues t) := by
      intro t ht
      obtain ⟨W',hW',hV⟩ := hCover t ht.1
      rcases Finset.mem_insert.mp hW' with he | hj
      · subst W'
        exact False.elim (ht.2 ⟨ht.1,hV⟩)
      · exact ⟨W',hj,hV⟩
    obtain ⟨D₂,hD₁D₂,hOutside⟩ := ih D₁ BPC (fun t ht => hF t ht.1) (fun t ht => hG t ht.1)
      hCoverC PC QC (hPC.trans hD₀D₁) (hQC.trans hD₀D₁) (hBPC.trans hD₀D₁)
      (hB.trans (hCD₀.trans hD₀D₁))
    let hD₀D₂ := hD₀D₁.trans hD₁D₂
    let hCD₂ := hCD₀.trans hD₀D₂
    let eP := indexedVolumeBinaryIso hc D₂ F BP E hET hEΓ P (hP.trans hCD₂) PA PC
      (hPA.trans hD₀D₂) (hPC.trans hD₀D₂)
    let eQ := indexedVolumeBinaryIso hc D₂ G BP E hET hEΓ Q (hQ.trans hCD₂) QA QC
      (hQA.trans hD₀D₂) (hQC.trans hD₀D₂)
    have hParts := (hInside.extend hD₁D₂).coprod hc D₂ hOutside
    exact ⟨D₂,hCD₂,((VolumeBlowupEquivalent.of_iso D₂ (eP.symm hc D₂)).trans hc D₂ hParts).trans hc D₂
      (VolumeBlowupEquivalent.of_iso D₂ eQ)⟩

end IntegrationInACVF.Section7
