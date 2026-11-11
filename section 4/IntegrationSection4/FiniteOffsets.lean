import IntegrationSection4.FiniteRVScalarImage

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section5

namespace IntegrationInACVF.Section4.FiniteOffsets

open TranslationOffsets

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

theorem finite_offset_range {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (G : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk G.real < κ)
    (T : SpecialBijection A B) (hT : GammaChainDefinable G T.chain) :
    (Set.range (offsetValue T)).Finite := by
  have hGraph := GammaOffsets.offset_function_graph T hT
  have hSingle (u : Point (M := M) 0 l) (v w : Point (M := M) 1 0)
      (hv : ∃ t : labelsImage B, t.val = u.2 ∧ vfAt v 0 = offsetValue T t)
      (hw : ∃ t : labelsImage B, t.val = u.2 ∧ vfAt w 0 = offsetValue T t) : vfAt v 0 = vfAt w 0 := by
    obtain ⟨t,ht,hv⟩ := hv
    obtain ⟨t',ht',hw⟩ := hw
    have he : t = t' := Subtype.ext (ht.trans ht'.symm)
    exact hv.trans (he.symm ▸ hw.symm)
  have hF := FiniteRVScalarImage.finite_image hκ hs G hsmall _ hGraph hSingle
  apply hF.subset
  rintro x ⟨t,rfl⟩
  exact ⟨(Fin.elim0,t.val),unaryPoint (offsetValue T t) Fin.elim0,⟨t,rfl,rfl⟩,rfl⟩

/-- Lemma 4.1 including its finite-range remark. The original Gamma base
is retained; genuine saturation is needed only for finiteness. -/
theorem lemma_4_1 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (G : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk G.real < κ)
    (T : SpecialBijection A B) (hT : GammaChainDefinable G T.chain)
    (hB : IsRVPullback (carrier B)) :
    GammaGraphDefinable G (fun (u : Point (M := M) 0 l) (z : Point (M := M) 1 0) =>
      ∃ t : labelsImage B, t.val = u.2 ∧ vfAt z 0 = offsetValue T t) ∧
      (Set.range (offsetValue T)).Finite ∧ ∀ b : B,
        (fun p : Point (M := M) 1 m => vfAt p 0) '' T.inverseFibre b =
          (fun x => x + offsetValue T (toLabels B b)) ''
            {x : VF (M := M) | rv x = rv (vfAt b.val 0)} :=
  ⟨GammaOffsets.offset_function_graph T hT,finite_offset_range hκ hs G hsmall T hT,
    inverse_fibre_translate T hB⟩

end IntegrationInACVF.Section4.FiniteOffsets
