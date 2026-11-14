import Integration7.NativeRelativeTranslations
import Mathlib.Data.Fin.VecNotation

/-! Exact VF-pair domains and images of actual native two-coordinate
maps. This connects set-level cell equivalences to their native images. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def twoVFPointPairEquiv : Point (M := M) 2 0 ≃ VF (M := M) × VF (M := M) where
  toFun p := (p.1 0,p.1 1)
  invFun z := (![z.1,z.2],Fin.elim0)
  left_inv p := by
    refine Prod.ext ?_ (Subsingleton.elim _ _)
    funext i
    fin_cases i <;> rfl
  right_inv _ := rfl

def nativeVFPairDomain (A : DefSet (M := M) S 2 0) : Set (VF (M := M) × VF (M := M)) :=
  twoVFPointPairEquiv '' carrier A

theorem mem_native_vf_pair_domain (A : DefSet (M := M) S 2 0) (p : Point (M := M) 2 0) :
    twoVFPointPairEquiv p ∈ nativeVFPairDomain A ↔ p ∈ carrier A := by
  constructor
  · rintro ⟨q,hq,he⟩
    exact twoVFPointPairEquiv.injective he ▸ hq
  · intro hp
    exact ⟨p,hp,rfl⟩

theorem native_vf_pair_map_image (A : DefSet (M := M) S 2 0)
    (F : Map A (PresentedSet.univ (pointSpace 2 0) S))
    (Q : Set (VF (M := M) × VF (M := M))) (e : nativeVFPairDomain A ≃ Q)
    (hF : ∀ p : A, twoVFPointPairEquiv (F p).val =
      (e ⟨twoVFPointPairEquiv p.val,⟨p.val,p.property,rfl⟩⟩).val) :
    nativeVFPairDomain (Map.image F) = Q := by
  ext z
  constructor
  · rintro ⟨q,⟨p,rfl⟩,rfl⟩
    rw [hF p]
    exact (e ⟨twoVFPointPairEquiv p.val,⟨p.val,p.property,rfl⟩⟩).property
  · intro hz
    obtain ⟨q,hq,hqp⟩ := (e.symm ⟨z,hz⟩).property
    let p : A := ⟨q,hq⟩
    have hpre : (⟨twoVFPointPairEquiv p.val,⟨p.val,p.property,rfl⟩⟩ : nativeVFPairDomain A) =
        e.symm ⟨z,hz⟩ := Subtype.ext hqp
    refine ⟨(F p).val,⟨p,rfl⟩,?_⟩
    exact (hF p).trans ((congrArg (fun w => (e w).val) hpre).trans
      (congrArg Subtype.val (e.apply_symm_apply ⟨z,hz⟩)))

end IntegrationInACVF.Section7
