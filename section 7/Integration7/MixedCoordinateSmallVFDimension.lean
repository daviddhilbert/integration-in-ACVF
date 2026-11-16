module

public import Integration7.NativeVolumeDomains
public import Section4.CoordinateMaps

@[expose] public section

/-! A mixed two-VF domain has dimension at most one when one VF
coordinate together with the carried RV labels determines the other. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (VF carrier vfAt)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m : ℕ}

theorem mixed_vf_dimension_le_one_of_coordinate
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) S 2 m) (i : Fin 2)
    (hDet : ∀ p q : A, vfAt p.val i = vfAt q.val i → p.val.2 = q.val.2 → p.val.1 = q.val.1) :
    vfDim (rawRVSpace (M := M) 1) (rawSpecialSet hc A) ≤ 1 := by
  let f := vfSelect (fun _ : Fin 1 => i) (rawSpecialSet hc A)
  have hf : Function.Injective f := by
    intro p q he
    have hh := congrArg Subtype.val he
    have hVF := congrArg Prod.fst hh
    have hr := congrArg Prod.snd hh
    have hv : p.val.1 i = q.val.1 i := congrFun hVF 0
    exact Subtype.ext (Prod.ext (hDet ⟨p.val,p.property⟩ ⟨q.val,q.property⟩ hv hr) hr)
  exact (vfDim_le_of_finite_map (rawRVSpace (M := M) 1) f
    (Map.finiteFibres_of_injective hf)).trans (vfDim_le_arity _ _)

end IntegrationInACVF.Section7
