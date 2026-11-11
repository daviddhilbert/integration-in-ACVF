import IntegrationSection3ACVF.ThinComponentConservation
import IntegrationSection3ACVF.NormalizedThinFamilies
import IntegrationSection3ACVF.NormalizedNontrivialValue

/-! Lemma 3.22 over the full original real/Gamma/ball parameter base.
The actual finite families, VF graph and open-to-open property are the
inputs. No residue quotient map, constructibility or conservation theorem
is assumed. Canonical normalization preserves all actual point sets and
both finite counts before applying the proved canonical argument. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open scoped BigOperators
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF.PuncturedGeometry
open IntegrationInACVF.Section3ACVF.ThinFamilyGeometry

namespace IntegrationInACVF.Section3ACVF.ThinFamilyConservation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem lemma_3_22 (B : FullBaseAtomicity.Base (M := M))
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (F G : Finset (PuncturedBall M)) (hThinF : ∀ d ∈ F, IsThin d) (hThinG : ∀ d ∈ G, IsThin d)
    (hF : (F : Set (PuncturedBall M)).Pairwise (fun d e => Disjoint d.body e.body))
    (hG : (G : Set (PuncturedBall M)).Pairwise (fun d e => Disjoint d.body e.body))
    (f : M → M)
    (hf : FullBaseAtomicity.OverBase B {z : Fin 2 → M | z 0 ∈ body F ∧ z 1 = f (z 0)})
    (hbij : Set.BijOn f (body F) (body G)) (hoo : MaximalOpenClasses.OpenToOpen (body F) f) :
    F.card = G.card ∧ (∑ d : F, d.val.holes.card) = ∑ d : G, d.val.holes.card := by
  let N := @CanonicalStructure.normalize M sM
  have hN : @FirstOrder.Language.Theory.Model LRV M N Axioms.ACVF :=
    @CanonicalStructure.normalized_model M sM hM
  letI := sM
  let FN := @NormalizedThinFamilies.family M sM hM F
  let GN := @NormalizedThinFamilies.family M sM hM G
  have hBodyF : @body M N FN = body F := NormalizedThinFamilies.body_family F
  have hBodyG : @body M N GN = body G := NormalizedThinFamilies.body_family G
  have hThinFN := NormalizedThinFamilies.thin_family F hThinF
  have hThinGN := NormalizedThinFamilies.thin_family G hThinG
  have hDisFN := NormalizedThinFamilies.disjoint_family F hF
  have hDisGN := NormalizedThinFamilies.disjoint_family G hG
  have hRaw : @Set.Definable M Set.univ LRV N (Fin 2)
      {z : Fin 2 → M | z 0 ∈ body F ∧ z 1 = f (z 0)} := by
    let p := @ParameterPresentation.presentation M sM hM
    letI := N
    obtain ⟨E,_,hE⟩ := ImaginaryParameters.OverBase.specialize (p := p) hf
    exact hE.mono (Set.subset_univ _)
  have hGraphN : @Set.Definable M Set.univ LRV N (Fin 2)
      {z : Fin 2 → M | z 0 ∈ @body M N FN ∧ z 1 = f (z 0)} := by
    rw [hBodyF]
    exact hRaw
  have hBijN : Set.BijOn f (@body M N FN) (@body M N GN) := by
    rw [hBodyF,hBodyG]
    exact hbij
  have hOpenN : @MaximalOpenClasses.OpenToOpen M N hN (@body M N FN) f := by
    intro D hD
    rw [NormalizedThinGeometry.open_normalize_iff D,
      NormalizedThinGeometry.open_normalize_iff (f '' D)]
    apply hoo D
    rwa [hBodyF] at hD
  obtain ⟨β,hβ⟩ := NormalizedNontrivialValue.exists_gt_one δ hδ
  have hCounts := @ThinComponentConservation.canonical M N hN
    (@CanonicalStructure.normalize_isCanonical M sM) β hβ FN GN
    hThinFN hThinGN hDisFN hDisGN f hGraphN hBijN hOpenN
  exact ⟨(NormalizedThinFamilies.card_family F).symm.trans
      (hCounts.1.trans (NormalizedThinFamilies.card_family G)),
    (NormalizedThinFamilies.holes_family F).symm.trans
      (hCounts.2.trans (NormalizedThinFamilies.holes_family G))⟩

end IntegrationInACVF.Section3ACVF.ThinFamilyConservation
