import IntegrationSection5.MixedRVRefinement
import IntegrationSection4.RVLabelAttachment

/-! Attaching an actual original-Gamma RV code is a definable bijection
onto its image and fixes every VF coordinate and every old RV label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5.RVAttachment
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m d : ℕ} {A : Set (Point (M := M) n m)}

def target (Q : GammaRVMap G A d) : Set (Point (M := M) n (m+d)) := Set.range Q.attachment

def toTarget (Q : GammaRVMap G A d) (a : A) : target Q := ⟨Q.attachment a,⟨a,rfl⟩⟩

theorem attachment_injective (Q : GammaRVMap G A d) : Function.Injective Q.attachment := by
  intro a b hab
  apply Subtype.ext
  refine Prod.ext (congrArg (fun q : Point (M := M) n (m+d) => q.1) hab) ?_
  funext j
  have h := congrArg (fun q : Point (M := M) n (m+d) => q.2 (Fin.castAdd d j)) hab
  simpa only [GammaRVMap.attachment,Fin.append_left] using h

theorem toTarget_bijective (Q : GammaRVMap G A d) : Function.Bijective (toTarget Q) := by
  constructor
  · intro a b hab
    exact attachment_injective Q (congrArg (fun q : target Q => q.val) hab)
  · rintro ⟨q,a,ha⟩
    exact ⟨a,Subtype.ext ha⟩

def gammaIso (Q : GammaRVMap G A d) : GammaIso G A (target Q) where
  equiv := Equiv.ofBijective (toTarget Q) (toTarget_bijective Q)
  graph := Q.attachment_graph

theorem target_definable (Q : GammaRVMap G A d) : GammaSetDefinable G (target Q) :=
  (gammaIso Q).target_definable (gammaLogicInput G)

theorem toTarget_vf (Q : GammaRVMap G A d) (a : A) (i : Fin n) :
    vfAt (toTarget Q a).val i = vfAt a.val i := rfl

theorem toTarget_oldLabels (Q : GammaRVMap G A d) (a : A) (j : Fin m) :
    (toTarget Q a).val.2 (Fin.castAdd d j) = a.val.2 j := Fin.append_left _ _ j

theorem toTarget_newLabels (Q : GammaRVMap G A d) (a : A) (j : Fin d) :
    (toTarget Q a).val.2 (Fin.natAdd m j) = Q.toFun a j := Fin.append_right _ _ j

variable {p : ℕ} {D : Set (Point (M := M) (p+1) m)}

theorem context_eq_iff (Q : GammaRVMap G D d) (a b : D) :
    MixedScalarFamilies.context (Q.attachment a) = MixedScalarFamilies.context (Q.attachment b) ↔
      MixedScalarFamilies.context a.val = MixedScalarFamilies.context b.val ∧ Q.toFun a = Q.toFun b := by
  constructor
  · intro h
    have ht := IntegrationInACVF.Section5.gammaPointCode_injective h
    have hv := congrArg (fun q : Point (M := M) p (m+d) => q.1) ht
    have hl := congrArg (fun q : Point (M := M) p (m+d) => q.2) ht
    have hold : a.val.2 = b.val.2 := by
      funext j
      have he := congrFun hl (Fin.castAdd d j)
      simpa only [dropHead,GammaRVMap.attachment,Fin.append_left,id_eq] using he
    refine ⟨congrArg gammaPointCode (Prod.ext hv hold),?_⟩
    funext j
    have he := congrFun hl (Fin.natAdd m j)
    simpa only [dropHead,GammaRVMap.attachment,Fin.append_right,id_eq] using he
  · rintro ⟨hc,hQ⟩
    have ht := IntegrationInACVF.Section5.gammaPointCode_injective hc
    apply congrArg gammaPointCode
    refine Prod.ext (congrArg (fun q : Point (M := M) p m => q.1) ht) ?_
    have hold := congrArg (fun q : Point (M := M) p m => q.2) ht
    change Fin.append a.val.2 (Q.toFun a) = Fin.append b.val.2 (Q.toFun b)
    change a.val.2 = b.val.2 at hold
    rw [hold,hQ]

end IntegrationInACVF.Section5.RVAttachment
