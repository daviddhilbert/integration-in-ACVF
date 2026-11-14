import Integration7.RVVolumeMorphisms
import IntegrationSection6.GammaRVGraphRaw
import IntegrationSection6.GammaTupleRelationPromotion

/-! Promote an actual essential chart with its explicit full original-
Gamma graph. Definability over a containing real context alone is not
used as a substitute for that original-base graph certificate. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {B : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}
variable {U V : PositiveRVVolumeObject (M := M) S k}

def rawVolumeIsoGraph (e : U.essential ≅ V.essential) :
    Set (Fin (U.underlying.obj.arity+V.underlying.obj.arity) → M) :=
  Set.range (fun u : U.essential.obj.domain => Fin.append (rvValues u.val) (rvValues (finiteIsoMap e u).val))

theorem rawVolumeIsoGraph_append_iff (e : U.essential ≅ V.essential)
    (x : Fin U.underlying.obj.arity → M) (y : Fin V.underlying.obj.arity → M) :
    Fin.append x y ∈ rawVolumeIsoGraph e ↔ ∃ u : U.essential.obj.domain,
      rvValues u.val = x ∧ rvValues (finiteIsoMap e u).val = y := by
  constructor
  · rintro ⟨u,hu⟩
    refine ⟨u,funext (fun i => ?_),funext (fun i => ?_)⟩
    · simpa only [Fin.append_left] using congrFun hu (Fin.castAdd V.underlying.obj.arity i)
    · simpa only [Fin.append_right] using congrFun hu (Fin.natAdd U.underlying.obj.arity i)
  · rintro ⟨u,rfl,rfl⟩
    exact ⟨u,rfl⟩

theorem rawVolumeIsoGraph_definable (e : U.essential ≅ V.essential)
    (hGraph : GammaGraphDefinable B
      (fun (x : Point (M := M) 0 U.underlying.obj.arity) (y : Point (M := M) 0 V.underlying.obj.arity) =>
        ∃ u : U.essential.obj.domain, u.val = x.2 ∧ (finiteIsoMap e u).val = y.2)) :
    DefinableOverBase B (fun _ => .rv) (rawVolumeIsoGraph e) := by
  have h := gammaRawRVGraph_definable hGraph
  convert h using 1
  ext w
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨(Fin.elim0,u.val),(Fin.elim0,(finiteIsoMap e u).val),⟨u,rfl,rfl⟩,rfl⟩
  · rintro ⟨x,y,⟨u,hx,hy⟩,hw⟩
    refine ⟨u,?_⟩
    change Fin.append (fun j => (u.val j).val) (fun j => ((finiteIsoMap e u).val j).val) = w
    have hx' := congrArg (fun v : Fin U.underlying.obj.arity → CanonicalRV.RVSort M => fun j => (v j).val) hx
    have hy' := congrArg (fun v : Fin V.underlying.obj.arity → CanonicalRV.RVSort M => fun j => (v j).val) hy
    exact (congrArg₂ Fin.append hx' hy').trans hw

theorem gamma_volume_chart_promotion (z : Fin p → M) (hz : ∀ i, sortEval (sp i) (z i))
    (e : U.essential ≅ V.essential)
    (hGraph : GammaGraphDefinable ⟨B.real ∪ Set.range z,B.gamma⟩
      (fun (x : Point (M := M) 0 U.underlying.obj.arity) (y : Point (M := M) 0 V.underlying.obj.arity) =>
        ∃ u : U.essential.obj.domain, u.val = x.2 ∧ (finiteIsoMap e u).val = y.2)) :
    ∃ H : Set (Fin ((p+U.underlying.obj.arity)+V.underlying.obj.arity) → M),
      DefinableOverBase B
        (Fin.append (Fin.append sp (fun _ : Fin U.underlying.obj.arity => .rv))
          (fun _ : Fin V.underlying.obj.arity => .rv)) H ∧
      ∀ x y, Fin.append (Fin.append z x) y ∈ H ↔
        ∃ u : U.essential.obj.domain, rvValues u.val = x ∧ rvValues (finiteIsoMap e u).val = y := by
  obtain ⟨H,hH,hHz⟩ := gamma_rv_tuple_relation_promotion B sp z hz (rawVolumeIsoGraph e)
    (rawVolumeIsoGraph_definable e hGraph)
  exact ⟨H,hH,fun x y => (hHz x y).trans (rawVolumeIsoGraph_append_iff e x y)⟩

end IntegrationInACVF.Section7
