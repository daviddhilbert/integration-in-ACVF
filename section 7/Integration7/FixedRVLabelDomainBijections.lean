module

public import Integration7.GammaFixedRVLabelSpecialLifts
public import IntegrationSection5.GammaGraphOperations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Adjoining a fixed RV tuple is a genuine definable bijection onto its
image. Arbitrary actual bijections lift with all fixed labels retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {n a b d : ℕ}

theorem fixed_rv_label_projection_bijective (A : DefSet (M := M) S n a)
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ S) :
    Function.Bijective (fixedRVLabelProjectionMap A z hz) := by
  constructor
  · intro p q he
    have h := congrArg Subtype.val he
    have hv0 := congrArg Prod.fst h
    have hv : p.val.1 = q.val.1 := hv0
    have hl0 := congrArg Prod.snd h
    have hl : p.val.2 ∘ Fin.castAdd d = q.val.2 ∘ Fin.castAdd d := hl0
    have hp := ((fixed_rv_label_domain_carrier A z hz p.val).mp p.property).2
    have hq := ((fixed_rv_label_domain_carrier A z hz q.val).mp q.property).2
    exact Subtype.ext (Prod.ext hv (fixed_rv_labels_jointly_determine _ _ hl (hp.trans hq.symm)))
  · intro p
    obtain ⟨q,hq⟩ := fixed_rv_label_projection_surjective A z hz p
    exact ⟨q,Subtype.ext hq⟩

theorem gamma_fixed_rv_label_projection (A : DefSet (M := M) S n a)
    (hA : GammaSetDefinable P (carrier A)) (z : Fin d → RV (M := M))
    (hz : ∀ j, (z j).val ∈ S)
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val}) :
    GammaGraphDefinable P (pointMapGraph (fixedRVLabelProjectionMap A z hz)) :=
  GammaGraphDefinable.congr (gamma_retain_vf_labels_graph (fixedRVLabelDomain A z hz) (Fin.castAdd d)
    (gamma_fixed_rv_label_domain A hA z hz hzΓ)) (fun _ _ => Iff.rfl)

def fixedRVLabelMap {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (f : Map A B) (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ S) :
    Map (fixedRVLabelDomain A z hz) (fixedRVLabelDomain B z hz) :=
  Map.comp (Map.inverse (fixedRVLabelProjectionMap B z hz) (fixed_rv_label_projection_bijective B z hz))
    (Map.comp f (fixedRVLabelProjectionMap A z hz))

theorem fixed_rv_label_map_bijective {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (f : Map A B) (hf : Function.Bijective f) (z : Fin d → RV (M := M))
    (hz : ∀ j, (z j).val ∈ S) : Function.Bijective (fixedRVLabelMap f z hz) := by
  let q := fixedRVLabelProjectionMap B z hz
  have hq := fixed_rv_label_projection_bijective B z hz
  have hInv : Function.Bijective (Map.inverse q hq) := by
    constructor
    · intro p p' he
      exact (Map.apply_inverse q hq p).symm.trans ((congrArg q he).trans (Map.apply_inverse q hq p'))
    · intro p
      exact ⟨q p,Map.inverse_apply q hq p⟩
  exact hInv.comp (hf.comp (fixed_rv_label_projection_bijective A z hz))

theorem fixed_rv_label_map_vf {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (f : Map A B) (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ S)
    (p : fixedRVLabelDomain A z hz) :
    (fixedRVLabelMap f z hz p).val.1 = (f (fixedRVLabelProjectionMap A z hz p)).val.1 := by
  have h := congrArg (fun q : B => q.val.1)
    (Map.apply_inverse (fixedRVLabelProjectionMap B z hz) (fixed_rv_label_projection_bijective B z hz)
      (f (fixedRVLabelProjectionMap A z hz p)))
  exact h

theorem fixed_rv_label_map_relative {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (f : Map A B) {i : Fin n} (hi : UnaryRelative f i)
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ S) :
    UnaryRelative (fixedRVLabelMap f z hz) i := by
  intro p j hj
  rw [fixed_rv_label_map_vf]
  exact hi (fixedRVLabelProjectionMap A z hz p) j hj

theorem gamma_fixed_rv_label_map {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (f : Map A B) (hA : GammaSetDefinable P (carrier A)) (hB : GammaSetDefinable P (carrier B))
    (hf : GammaGraphDefinable P (pointMapGraph f))
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ S)
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val}) :
    GammaGraphDefinable P (pointMapGraph (fixedRVLabelMap f z hz)) := by
  have hAΓ := gamma_fixed_rv_label_projection A hA z hz hzΓ
  have hBΓ := gamma_fixed_rv_label_projection B hB z hz hzΓ
  have hInv := gamma_inverse_map_graph (fixedRVLabelProjectionMap B z hz)
    (fixed_rv_label_projection_bijective B z hz) hBΓ
  exact gamma_composition_graph _ _ (gamma_composition_graph _ _ hAΓ hf) hInv

end IntegrationInACVF.Section7
