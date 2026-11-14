import Integration7.NativeFixedRVLabels
import Integration7.ProductCoordinateSaturation
import Integration7.UnarySpecialHeadPreparations

/-! Exact first contractions of products with an RV class, retaining
every fixed old RV label. This identifies the actual remaining unary
domain with the domain used by the carried-label special construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a d : ℕ}

theorem fixed_pure_vf_label_domain_carrier (A : DefSet (M := M) S n 0)
    (t : Fin d → RV (M := M)) (ht : ∀ i, (t i).val ∈ S) (p : Point (M := M) n (0+d)) :
    p ∈ carrier (fixedRVLabelDomain A t ht) ↔ (p.1,Fin.elim0) ∈ carrier A ∧
      p.2 = Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) t := by
  have h := fixed_rv_label_domain_carrier A t ht p
  have he : retainVFLabels (Fin.castAdd d : Fin 0 → Fin (0+d)) p = (p.1,Fin.elim0) :=
    Prod.ext rfl (Subsingleton.elim _ _)
  rw [he] at h
  rw [h]
  constructor
  · rintro ⟨hp,ht⟩
    refine ⟨hp,?_⟩
    calc
      p.2 = Fin.append (p.2 ∘ Fin.castAdd d) (p.2 ∘ Fin.natAdd 0) := Fin.append_castAdd_natAdd.symm
      _ = Fin.append Fin.elim0 t := congrArg₂ Fin.append (Subsingleton.elim _ _) ht
  · rintro ⟨hp,he'⟩
    refine ⟨hp,?_⟩
    rw [he']
    exact funext fun i => Fin.append_right _ _ i

theorem head_saturated_fixed_rv_labels (A : DefSet (M := M) S (n+1) a)
    (hA : HeadSaturated (carrier A)) (t : Fin d → RV (M := M)) (ht : ∀ i, (t i).val ∈ S) :
    HeadSaturated (carrier (fixedRVLabelDomain A t ht)) := by
  intro p hp x hx
  have h := (fixed_rv_label_domain_carrier A t ht p).mp hp
  apply (fixed_rv_label_domain_carrier A t ht (replace 0 p x)).mpr
  exact ⟨hA _ h.1 x hx,h.2⟩

def saturatedIdentityPreparation (A : DefSet (M := M) S (n+1) a)
    (hA : HeadSaturated (carrier A)) : HeadPreparation A :=
  ⟨a,A,Map.id A,specialRelative_id A 0,hA⟩

theorem prepend_rv_label_tuple_names (r : RV (M := M)) (hr : r.val ∈ S)
    (t : Fin d → RV (M := M)) (ht : ∀ i, (t i).val ∈ S) :
    ∀ i, ((Fin.append (fun _ : Fin 1 => r) t) i).val ∈ S := by
  intro i
  cases i using Fin.addCases with
  | left j => simpa only [Fin.append_left] using hr
  | right j => simpa only [Fin.append_right] using ht j

set_option maxHeartbeats 800000 in
theorem head_image_fixed_rv_class_product_carrier
    (A : DefSet (M := M) S 2 0) (B : DefSet (M := M) S 1 0)
    (r : RV (M := M))
    (hProduct : ∀ p : Point (M := M) 2 0, p ∈ carrier A ↔
      rv (vfAt p 0) = r ∧ ((fun _ : Fin 1 => vfAt p 1),Fin.elim0) ∈ carrier B)
    (t : Fin d → RV (M := M)) (ht : ∀ i, (t i).val ∈ S)
    (q : Point (M := M) 1 (1+(0+d))) :
    q ∈ carrier (headImage (fixedRVLabelDomain A t ht)) ↔ (q.1,Fin.elim0) ∈ carrier B ∧
      q.2 = Fin.append (fun _ : Fin 1 => r) (Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) t) := by
  constructor
  · rintro ⟨p,he⟩
    have hp := (fixed_pure_vf_label_domain_carrier A t ht p.val).mp p.property
    have hpr := (hProduct (p.val.1,Fin.elim0)).mp hp.1
    have he' : headKey p.val = q := (headKeyMap_apply _ p).symm.trans he
    have hq : (show Point (M := M) 1 0 from (q.1,Fin.elim0)) =
        ((fun _ : Fin 1 => vfAt (p.val.1,Fin.elim0) 1),Fin.elim0) := by
      refine Prod.ext ?_ rfl
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact (congrArg (fun z : Point (M := M) 1 (1+(0+d)) => z.1 0) he').symm
    refine ⟨(congrArg (fun z : Point (M := M) 1 0 => z ∈ carrier B) hq).mpr hpr.2,?_⟩
    have hlabels := congrArg Prod.snd he'
    change Fin.append (fun _ : Fin 1 => rv (vfAt p.val 0)) p.val.2 = q.2 at hlabels
    exact hlabels.symm.trans (by rw [hp.2]; exact congrArg (fun z => Fin.append (fun _ : Fin 1 => z) (Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) t)) hpr.1)
  · rintro ⟨hq,he⟩
    obtain ⟨x,hx⟩ := CanonicalRV.encodedRv_surjective r
    have hx' : rv x = r := by
      apply Subtype.ext
      exact congrArg Subtype.val hx
    let p₀ : Point (M := M) 2 0 := (![x,q.1 0],Fin.elim0)
    have hp₀ : p₀ ∈ carrier A := by
      apply (hProduct p₀).mpr
      refine ⟨hx',?_⟩
      have hPoint : (show Point (M := M) 1 0 from ((fun _ : Fin 1 => vfAt p₀ 1),Fin.elim0)) =
          (q.1,Fin.elim0) := by
        refine Prod.ext ?_ rfl
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
      exact (congrArg (fun z : Point (M := M) 1 0 => z ∈ carrier B) hPoint).mpr hq
    let p : fixedRVLabelDomain A t ht := Map.toImage (appendFixedRVLabelsMap A t ht) ⟨p₀,hp₀⟩
    refine ⟨p,(headKeyMap_apply _ p).trans ?_⟩
    refine Prod.ext ?_ ?_
    · funext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
    · change Fin.append (fun _ : Fin 1 => rv x) (Fin.append (Fin.elim0 : Fin 0 → RV (M := M)) t) = q.2
      rw [hx',he]

end IntegrationInACVF.Section7
