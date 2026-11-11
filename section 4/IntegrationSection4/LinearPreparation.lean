import IntegrationSection4.PreparedLinearity
import IntegrationSection3ACVF.FullOpenToOpenPartition
import IntegrationSection3ACVF.AdjoinGamma

/-! Lemma 4.2. Prepare the full radius/slope relation and the finite
open-to-open partition simultaneously over the original Gamma base.
The final witness is an actual special bijection, not an existence input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.LinearPreparation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem lemma_4_2 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (hGenerated : GammaParameters.VFGammaGeneratedBase G)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ)
    (A C : Set M) (hA : GammaParameters.DefinableAtBase G .vf A)
    (hCVF : C ⊆ {x | iVF x}) (f : M → M)
    (hf : GammaParameters.DefinableOverBase G (fun _ : Fin 2 => .vf) (ImaginaryBaseImages.graphOn A f))
    (hbij : Set.BijOn f A C) :
    ∃ l : ℕ, ∃ E : Set (Point (M := M) 1 l),
      ∃ T : GammaSpecialBijection G (GammaUnarySyntax.pointSet A) E,
        IsRVPullback E ∧ ∀ b : T.target,
          ∃ hBA : InverseBodies.body T.special b ⊆ A,
            (∃ s : Values.Gamma (M := M), GammaLinearity.GammaLinear (InverseBodies.body T.special b) f
              (fun x hx => hCVF (hbij.1 (hBA hx))) s) ∧
            MaximalOpenClasses.OpenToOpen (InverseBodies.body T.special b) f := by
  let B := GammaBaseBridge.fullBase G
  have hAVF : A ⊆ {x | iVF x} := fun x hx => hA.proper x hx
  have hfVF : ∀ x ∈ A, iVF (f x) := fun x hx => hCVF (hbij.1 hx)
  have hAF : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A} := GammaBaseBridge.of_gamma G hA
  have hfF : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f) := GammaBaseBridge.of_gamma G hf
  have hδF : FullGammaSyntax.Scalar B {δ} := AdjoinGamma.named_scalar δ ⟨δ,hδ,rfl⟩
  obtain ⟨P,hP,_,hCover⟩ := FullOpenToOpenPartition.proposition_3_19 hκ hs B hsmall h00 δ hδF hδ1
    hAF hAVF hCVF f hfF hbij
  have hPoint := GammaUnarySyntax.pointSet_definable G A hA
  obtain ⟨d,t,_,D,hD⟩ := gammaPresentationInput G (GammaUnarySyntax.pointSet A) hPoint
  let S := G.real ∪ Set.range (rawTuple t)
  have hGS : G.real ⊆ S := Set.subset_union_left
  have hDG : GammaSetDefinable G (carrier D) := hD.symm ▸ hPoint
  have hRowG := GammaUnarySyntax.linearRow_definable G A f hfF
  obtain ⟨l,E,T,hTa,hTG,hE,hRows⟩ := GammaRelationPreparation.prepare hs h00 G hsmall hGenerated hGS
    D hDG (GammaUnarySyntax.linearRow A f) hRowG none (by intro h; cases h)
  have hPieces (U : P) : GammaParameters.DefinableAtBase G .vf U.val := by
    apply GammaBaseDescent.to_gamma G (fun _ : Fin 1 => .vf) {z | z 0 ∈ U.val} (hP U.val U.property).2.2.1
    intro z hz i
    fin_cases i
    exact hAVF ((hP U.val U.property).2.1 hz)
  let rPiece (U : P) (p : Point (M := M) 1 0) (_ : Point (M := M) 0 0) : Prop :=
    (vfAt p 0).val ∈ U.val
  have hrPiece (U : P) : GammaGraphDefinable G (rPiece U) :=
    GammaUnarySyntax.membership_definable G U.val (hPieces U)
  obtain ⟨q,F,W,hWG,hF,hRef,hPrepared⟩ := FiniteRelationPreparation.prepare_finite hs h00 G hsmall
    hGenerated hGS T hTG hE rPiece hrPiece Finset.univ
  have hRowsW : FiniteRelationPreparation.Uniform (GammaUnarySyntax.linearRow A f) W :=
    FiniteRelationPreparation.Uniform.refine hRows hRef
  let V : GammaSpecialBijection G (GammaUnarySyntax.pointSet A) (carrier F) :=
    ⟨S,hGS,D,F,hD,rfl,W,hWG⟩
  refine ⟨q,carrier F,V,hF,?_⟩
  intro b
  change ∃ hBA : InverseBodies.body W b ⊆ A,
    (∃ s : Values.Gamma (M := M), GammaLinearity.GammaLinear (InverseBodies.body W b) f
      (fun x hx => hCVF (hbij.1 (hBA hx))) s) ∧ MaximalOpenClasses.OpenToOpen (InverseBodies.body W b) f
  have hBA : InverseBodies.body W b ⊆ A := by
    rintro x ⟨a,ha,_⟩
    have hh := (Set.ext_iff.mp hD a.val).mp a.property
    change (vfAt a.val 0).val ∈ A at hh
    rwa [ha] at hh
  refine ⟨hBA,PreparedLinearity.linear_on_body hκ hs B hsmall h00 A f hfF hfVF hbij.2.1 W hF hRowsW b hBA,?_⟩
  let x₀ := (vfAt (W.inverseMap b).val 0).val
  have hx₀ : x₀ ∈ InverseBodies.body W b := by
    exact ⟨W.inverseMap b,rfl,by rw [W.apply_inverse]; rfl⟩
  obtain ⟨U,hUP,hxU⟩ := (Set.ext_iff.mp hCover x₀).mp (hBA hx₀)
  let u : P := ⟨U,hUP⟩
  have hBodyU : InverseBodies.body W b ⊆ U := by
    rintro x ⟨a,ha,he⟩
    have hh := hPrepared u (Finset.mem_univ u) (W.toMap a) b he (Fin.elim0,Fin.elim0)
    change (vfAt (W.inverseMap (W.toMap a)).val 0).val ∈ U ↔ x₀ ∈ U at hh
    rw [W.inverse_apply] at hh
    have hMem := hh.mpr hxU
    rwa [ha] at hMem
  intro Q hQ
  exact (hP U hUP).2.2.2 Q (hQ.trans hBodyU)

end IntegrationInACVF.Section4.LinearPreparation
