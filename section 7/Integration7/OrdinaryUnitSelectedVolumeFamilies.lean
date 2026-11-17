module

public import Integration7.OrdinaryVFVolumeFamilies
public import Integration7.SelectedVolumeFamilies
public import Integration7.SelectedVolumeRowContexts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! An ordinary family has a genuine positive presentation on the
density graph of its unit VF form. Its single selected coordinate and
its density are both one, and finite fibres remain actual finite fibres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a : ℕ}

def OrdinaryVFVolumeFamily.unitSelectedFamily (F : OrdinaryVFVolumeFamily C (n+1) a) :
    SelectedVFVolumeFamily C (n+1) (a+1) 0 where
  domain := F.fullVFObject.densityGraph.domain
  selected := fun _ => Fin.last a
  finite_selected x _ := (F.fullVFObject.densityGraph.finite_labels x).subset (fun _ h => h.1)
  form := F.fullVFObject.densityGraph.form

theorem ordinary_unit_selected_form_one (F : OrdinaryVFVolumeFamily C (n+1) a)
    (q : F.unitSelectedFamily.domain) : F.unitSelectedFamily.form.value q=1 := rfl

theorem ordinary_unit_selected_density_label (F : OrdinaryVFVolumeFamily C (n+1) a)
    (q : F.unitSelectedFamily.domain) : q.val.2 (Fin.last a)=1 :=
  (densityGraph_form_last F.fullVFObject q).symm.trans (ordinary_unit_selected_form_one F q)

theorem ordinary_unit_selected_form_retained (F : OrdinaryVFVolumeFamily C (n+1) a)
    (q : F.unitSelectedFamily.domain) : F.unitSelectedFamily.form.value q=q.val.2 (Fin.last a) :=
  densityGraph_form_last F.fullVFObject q

theorem ordinary_unit_selected_row_coordinates (F : OrdinaryVFVolumeFamily C (n+1) a)
    (x : Fin (n+1) → VFType (M := M)) (r : (F.unitSelectedFamily.rowInContext x).underlying.obj.domain) :
    (F.unitSelectedFamily.rowInContext x).underlying.obj.value r = fun _ => 1 := by
  funext i
  exact ordinary_unit_selected_density_label F ⟨(x,r.val),r.property⟩
end IntegrationInACVF.Section7
