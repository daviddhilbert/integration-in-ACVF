import Integration7.DensityGraphVolumeBijections
import Integration7.NativeVolumeMapRealization
import IntegrationSection5.RelativelyUnary

/-! Passing to actual density graphs retains the original relatively
unary VF-coordinate behavior. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem VFVolumeBijection.onDensityGraphs_relative
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k}
    (f : VFVolumeBijection U V) (i : Fin (k+1))
    (hi : ∀ p : U.domain, ∀ j, j ≠ i → (f.map p).val.1 j = p.val.1 j) :
    UnaryRelative (nativeMixedVolumeMap hc (f.onDensityGraphs hc C).map) i := by
  intro p j hj
  let e := volumeDensityGraphBijection hc C U
  let q := e.map.inverse e.bijective ⟨p.val,p.property⟩
  have hq : q.val.1 = p.val.1 :=
    congrArg (fun z => z.val.1) (Map.apply_inverse e.map e.bijective ⟨p.val,p.property⟩)
  change (f.map q).val.1 j = p.val.1 j
  exact (hi q j hj).trans (congrFun hq j)

end IntegrationInACVF.Section7
