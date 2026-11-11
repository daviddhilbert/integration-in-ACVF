import IntegrationSection5.FocusRefinement
import IntegrationSection5.PreparedInverseGeometry
import IntegrationSection5.UnarySpecialZeros

/-! Marked target focuses give the zero-point condition required by the
reverse contractibility refinement. No such condition is assumed of the
source focus: it follows from its actual pulled-section construction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m l r : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
variable {F : DefSet (M := M) S 1 r} {j : Fin m} {k : Fin l}

theorem matched_focus_zero_preimages (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (D : Focus B 0 k)
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    (hTag : Tagged (carrier A) 0 j) (R : SpecialBijection B F)
    (hMark : ∀ b : B, b.val ∈ D.locus →
      vfAt (R.toMap (focusSectionMap D hB b)).val 0 = 0) :
    ∀ z : F,
      ((Map.comp (Map.inverse f hf) R.inverseMap) z).val ∈ (pulledFocus f hf hc D hA hB hTag).locus →
      vfAt ((Map.comp (Map.inverse f hf) R.inverseMap) z).val 0 =
        (pulledFocus f hf hc D hA hB hTag).center ((Map.comp (Map.inverse f hf) R.inverseMap) z).val →
      vfAt z.val 0 = 0 := by
  intro z hp hcoord
  let p := (Map.comp (Map.inverse f hf) R.inverseMap) z
  have hsel : PullSelected f hf D hB p := by
    change p.val ∈ pulledFocusLocus f hf D hB at hp
    obtain ⟨a, ha, hs⟩ := hp
    have he : a = p := Subtype.ext ha
    exact he ▸ hs
  have hpull : p = pulledFocusSection f hf D hB p := by
    apply Subtype.ext
    refine Prod.ext ?_ ((sameRV_iff _ _).mp hsel.2).2.symm
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change vfAt p.val 0 = vfAt (pulledFocusSection f hf D hB p).val 0
    exact hcoord.trans (pulledFocusCentre_apply f hf D hB p)
  have hfp : f p = focusSectionMap D hB (f p) :=
    (congrArg f hpull).trans (map_pulledFocusSection f hf D hB p)
  have hzero : vfAt (R.toMap (f p)).val 0 = 0 := by
    rw [hfp]
    exact hMark (f p) hsel.1
  have he : R.toMap (f p) = z := by
    change R.toMap (f (Map.inverse f hf (R.inverseMap z))) = z
    rw [Map.apply_inverse, R.apply_inverse]
  exact he ▸ hzero

theorem matched_focus_reverse_contractible (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (hg : CellwiseOpenEquivalence f) (D : Focus B 0 k)
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    (hF : IsRVPullback (carrier F)) (hTag : Tagged (carrier A) 0 j)
    (R : SpecialBijection B F)
    (hFinal : Contractible (Map.comp (Map.inverse f hf) R.inverseMap))
    (hMark : ∀ b : B, b.val ∈ D.locus →
      vfAt (R.toMap (focusSectionMap D hB b)).val 0 = 0) :
    Contractible (Map.comp (focussedCanonical (pulledFocus f hf hc D hA hB hTag)).toMap
      (Map.comp (Map.inverse f hf) R.inverseMap)) := by
  exact focused_post_contractible _ hFinal (prepared_inverse_open_images f hf hg R hFinal) hF
    (pulledFocus f hf hc D hA hB hTag)
    (matched_focus_zero_preimages f hf hc D hA hB hTag R hMark)

end IntegrationInACVF.Section5
