import IntegrationSection5.PulledFocusDefinability
import IntegrationSection5.UnaryFocusImages
import IntegrationSection5.UnaryCanonicalImages
import IntegrationSection5.UnaryInverseGeometry

/-! The forward part of the matched-focus step in Lemma 5.2. -/

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
variable {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
variable {j : Fin m} {k : Fin l}

theorem unaryShift_zero (p : Point (M := M) 1 m) : unaryShift 0 p = p := by
  refine Prod.ext ?_ rfl
  funext i
  exact sub_zero _

theorem matched_focus_contractible (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (ho : CellwiseOpenMap f) (D : Focus B 0 k)
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    (hTag : Tagged (carrier A) 0 j) :
    Contractible
      (Map.comp (SpecialBijection.centripetal D).toMap
        (Map.comp f (focussedCanonical (pulledFocus f hf hc D hA hB hTag)).inverseMap)) := by
  let DA := pulledFocus f hf hc D hA hB hTag
  let T := focussedCanonical DA
  let g := Map.comp (SpecialBijection.centripetal D).toMap f
  have hT : IsRVPullback (carrier (canonicalImage DA.etaImage)) := T.preserves_pullback hA
  intro a b hab
  let p := T.inverseMap a
  let q := T.inverseMap b
  have hpq : SameRV p.val q.val := T.inverse_contractible a b hab
  have hfpq := hc p q hpq
  let c := focusClassShift D (f p)
  by_cases hc0 : c = 0
  · change SameRV (D.toFocusGeometry.eta (f p).val) (D.toFocusGeometry.eta (f q).val)
    rw [unary_focus_eta_eq_shift D (f p) (f p) rfl,
      unary_focus_eta_eq_shift D (f p) (f q) hfpq]
    change SameRV (unaryShift c (f p).val) (unaryShift c (f q).val)
    rw [hc0, unaryShift_zero, unaryShift_zero]
    exact hfpq
  · have hact : (f p).val ∈ D.locus := by
      by_contra h
      exact hc0 (by simp [c, focusClassShift, h])
    by_cases ha0 : vfAt a.val 0 = 0
    · have he : a = b := Subtype.ext (eq_of_sameRV_of_zero hab ha0)
      subst b
      rfl
    · let E := T.inverseFibre a
      obtain ⟨hE, hcell⟩ := T.remark_5_3 hT a ha0
      have hEA : E ⊆ carrier A := by
        rintro z ⟨x, he, hx⟩
        exact he ▸ x.property
      have hgo : CellwiseOpenMap g :=
        cellwiseOpenMap_comp f (SpecialBijection.centripetal D).toMap hc ho
          (focus_primitive_open_images D)
      have hImage : IsUnaryOpenPolydisc (unaryImage g E) := hgo E hE hEA ⟨p, hcell⟩
      have hpa : p.val ∈ E := by
        refine ⟨p, rfl, ?_⟩
        change SameRV (T.toMap (T.inverseMap a)).val a.val
        rw [T.apply_inverse]
        rfl
      have hqb : q.val ∈ E := by
        refine ⟨q, rfl, ?_⟩
        change SameRV (T.toMap (T.inverseMap b)).val a.val
        rw [T.apply_inverse]
        exact hab.symm
      apply unary_open_polydisc_sameRV hImage ?_ ⟨p, hpa, rfl⟩ ⟨q, hqb, rfl⟩
      rintro z ⟨x, hx, rfl⟩ hz
      have hxpRV : SameRV x.val p.val := hcell hx
      have hfpx := hc p x hxpRV.symm
      have hzero : vfAt (unaryShift c (f x).val) 0 = 0 := by
        rw [← unary_focus_eta_eq_shift D (f p) (f x) hfpx]
        exact hz
      have hfxcoord : vfAt (f x).val 0 = D.center (f p).val := by
        have h := (unaryShift_eq_zero_iff c (f x).val).mp hzero
        simpa only [c, focusClassShift, if_pos hact] using h
      have hfx : f x = focusSectionMap D hB (f p) := by
        apply Subtype.ext
        rw [focusSectionMap_active D hB (f p) hact]
        refine Prod.ext ?_ ((sameRV_iff _ _).mp hfpx).2.symm
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        change vfAt (f x).val 0 = D.center (f p).val
        exact hfxcoord
      have hxp : x = pulledFocusSection f hf D hB p :=
        hf.1 (hfx.trans (map_pulledFocusSection f hf D hB p).symm)
      have hsel : PullSelected f hf D hB x :=
        hxp.symm ▸ pullSelected_section f hf D hB p hact
      have hpullx : pulledFocusSection f hf D hB x = x := by
        rw [hxp, pulledFocusSection_idempotent]
      have hcx : DA.center x.val = vfAt x.val 0 := by
        change pulledFocusCentre f hf D hB x.val = _
        rw [pulledFocusCentre_apply, hpullx]
      have hxact : x.val ∈ DA.locus := ⟨x, rfl, hsel⟩
      have hTzero : vfAt (T.toMap x).val 0 = 0 := by
        change (DA.toFocusGeometry.eta x.val).1 0 = 0
        rw [FocusGeometry.eta, if_pos hxact]
        change vfAt x.val 0 - DA.center x.val = 0
        rw [hcx, sub_self]
      obtain ⟨y, hy, hya⟩ := hx
      have hyx : y = x := Subtype.ext hy
      have hxa : SameRV (T.toMap x).val a.val := hyx ▸ hya
      exact ha0 ((sameRV_zero_iff hxa).mp hTzero)

end IntegrationInACVF.Section5
