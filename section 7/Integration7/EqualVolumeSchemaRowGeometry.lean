import Integration7.GammaVolumeRelabelGeometry
import Integration7.GammaEqualLabelEquivalenceGraphs
import Integration7.VolumeSchemaRowSemantics

/-! Full coordinate and density rows identify the actual volume objects,
including arbitrary label arities. Their identity on labels has an
original-Gamma graph and realizes an actual volume isomorphism. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable gammaLogicInput)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B B₀ : Base (M := M)} {p k : ℕ} {sp : Fin p → SortTag}

set_option maxHeartbeats 1600000 in
theorem gamma_equal_volume_schema_rows_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (ha : U.underlying.obj.arity = V.underlying.obj.arity)
    (F : GammaRVVolumeSchema B₀ p U.underlying.obj.arity k sp) (z : Fin p → M)
    (P : RVVolumeSchemaRow U F z) (Q : RVVolumeSchemaRow V (ha ▸ F) z)
    (hU : VolumeObjectGamma U B) (hBC : B.real ⊆ (C.base : Set M)) :
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      ∃ f : RVVolumeIso (U.extend hCD) (V.extend hCD), f.GammaDefinable B := by
  rcases U with ⟨⟨⟨a,A,f⟩,hf⟩,ω⟩
  rcases V with ⟨⟨⟨b,E,g⟩,hg⟩,π⟩
  change a = b at ha
  cases ha
  have hAE : A.carrier = E.carrier := by
    ext x
    constructor
    · intro hx
      let u : A := ⟨x,hx⟩
      obtain ⟨v,hv,_⟩ := (Q.volume_iff x (f u).val).mp ((P.volume_iff x (f u).val).mpr ⟨u,rfl,rfl⟩)
      exact hv ▸ v.property
    · intro hx
      let v : E := ⟨x,hx⟩
      obtain ⟨u,hu,_⟩ := (P.volume_iff x (g v).val).mp ((Q.volume_iff x (g v).val).mpr ⟨v,rfl,rfl⟩)
      exact hu ▸ u.property
  let e : A ≃ E := {
    toFun := fun u => ⟨u.val,hAE ▸ u.property⟩
    invFun := fun v => ⟨v.val,hAE.symm ▸ v.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hcoord (u : A) : (g (e u)).val = (f u).val := by
    obtain ⟨v,hv,he⟩ := (Q.volume_iff u.val (f u).val).mp
      ((P.volume_iff u.val (f u).val).mpr ⟨u,rfl,rfl⟩)
    have hv' : v = e u := Subtype.ext hv
    exact (congrArg (fun v => (g v).val) hv').symm.trans he
  have hDensity (u : A) : π.value (e u) = ω.value u := by
    obtain ⟨v,hv,he⟩ := (Q.density_iff u.val (ω.map u).val).mp
      ((P.density_iff u.val (ω.map u).val).mpr ⟨u,rfl,rfl⟩)
    have hv' : v = e u := Subtype.ext hv
    exact congrFun ((congrArg (fun v => (π.map v).val) hv').symm.trans he) 0
  have hDomain : GammaSetDefinable B {x : Point (M := M) 0 a | x.2 ∈ A.carrier} := by
    have h := (gammaLogicInput B).image_graph ((gammaLogicInput B).swap_graph hU.coordinates)
    convert h using 1
    ext x
    constructor
    · intro hx
      exact ⟨(Fin.elim0,(f ⟨x.2,hx⟩).val),⟨x.2,hx⟩,rfl,rfl⟩
    · rintro ⟨y,u,hu,_⟩
      change x.2 ∈ A.carrier
      exact hu ▸ u.property
  have hGraph := gamma_equal_label_equivalence_graph A.carrier E.carrier hDomain e (fun _ => rfl)
  exact gammaVolumeRelabelRealizeWithGraph hc C e hGraph hcoord hDensity hBC hU

end IntegrationInACVF.Section7
