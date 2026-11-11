import IntegrationSection4.GammaRVMaps
import IntegrationSection4.GammaGraphOperations

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.UniformPositionGraphs

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def relation {G : GammaParameters.Base (M := M)} {m d : ℕ}
    {D : Set (Point (M := M) 1 m)} (g : D → VF (M := M)) (Q : GammaRVMap G D d)
    (s : Point (M := M) 0 d) (z : Point (M := M) 2 0) : Prop :=
  ∃ u : D, Q.toFun u = s.2 ∧ vfAt u.val 0 = vfAt z 0 ∧ g u = vfAt z 1

/-- The complete positioning graph, with the final RV label free. The
intermediate mixed point and both of its function values are quantified. -/
theorem definable {G : GammaParameters.Base (M := M)} {m d : ℕ}
    {D : Set (Point (M := M) 1 m)} (g : D → VF (M := M)) (Q : GammaRVMap G D d)
    (hg : GammaScalarGraphDefinable G (fun p y => ∃ u : D, u.val = p ∧ g u = y)) :
    GammaGraphDefinable G (relation g Q) := by
  let B := GammaBaseBridge.fullBase G
  let a := Fin ((0+d)+(2+0))
  let ι := a ⊕ Fin (1+m)
  let x : a := Fin.natAdd (0+d) (Fin.castAdd 0 (0 : Fin 2))
  let y : a := Fin.natAdd (0+d) (Fin.castAdd 0 (1 : Fin 2))
  let σQ : Fin ((1+m)+(0+d)) → ι := Fin.addCases Sum.inr
    (Fin.addCases (fun i : Fin 0 => i.elim0) (fun i => .inl (Fin.castAdd (2+0) (Fin.natAdd 0 i))))
  let σg : Fin ((1+m)+(1+0)) → ι := Fin.addCases Sum.inr
    (Fin.addCases (fun _ : Fin 1 => .inl y) (fun i : Fin 0 => i.elim0))
  let rQ (p : Point (M := M) 1 m) (q : Point (M := M) 0 d) := ∃ u : D, u.val = p ∧ Q.toFun u = q.2
  let rg (p : Point (M := M) 1 m) (q : Point (M := M) 1 0) := ∃ u : D, u.val = p ∧ g u = vfAt q 0
  have hQ := FullBaseAtomicity.OverBase.preimage_comp (GammaTupleGraphs.rawGraph_definable G rQ Q.graph) σQ
  have hG := FullBaseAtomicity.OverBase.preimage_comp (GammaTupleGraphs.rawGraph_definable G rg hg) σg
  have hEq : FullBaseAtomicity.OverBase B {z : ι → M | z (.inr (Fin.castAdd m (0 : Fin 1))) = z (.inl x)} := by
    apply FullBaseAtomicity.OverBase.of_real
    letI := @CanonicalStructure.normalize M sM
    exact RawClosure.definable_equal_coordinates B.real _ _
  let R : Set (a → M) := {z | ∃ w : Fin (1+m) → M,
    Sum.elim z w ∘ σQ ∈ GammaTupleGraphs.rawGraph rQ ∧
    Sum.elim z w ∘ σg ∈ GammaTupleGraphs.rawGraph rg ∧
    w (Fin.castAdd m 0) = z x}
  have hR : FullBaseAtomicity.OverBase B R :=
    FullBaseAtomicity.OverBase.exists_block (FullBaseAtomicity.OverBase.inter hQ
      (FullBaseAtomicity.OverBase.inter hG hEq))
  have h := GammaTupleGraphs.relation_of_full G R hR
  apply GammaGraphDefinable.congr h
  intro s z
  let Y : Point (M := M) 1 0 := (fun _ => vfAt z 1,Fin.elim0)
  have hQtuple (w : Fin (1+m) → M) :
      Sum.elim (Fin.append (gammaPointCode s) (gammaPointCode z)) w ∘ σQ =
        Fin.append w (gammaPointCode s) := by
    funext i
    cases i using Fin.addCases with
    | left i => simp only [Function.comp_apply,σQ,Fin.addCases_left,Sum.elim_inr,Fin.append_left]
    | right i =>
      cases i using Fin.addCases with
      | left i => exact i.elim0
      | right i => simp only [Function.comp_apply,σQ,Fin.addCases_right,Sum.elim_inl,
          Fin.append_left,Fin.append_right]
  have hGtuple (w : Fin (1+m) → M) :
      Sum.elim (Fin.append (gammaPointCode s) (gammaPointCode z)) w ∘ σg =
        Fin.append w (gammaPointCode Y) := by
    funext i
    cases i using Fin.addCases with
    | left i => simp only [Function.comp_apply,σg,Fin.addCases_left,Sum.elim_inr,Fin.append_left]
    | right i =>
      cases i using Fin.addCases with
      | left i => simp only [Function.comp_apply,σg,Fin.addCases_right,Fin.addCases_left,Sum.elim_inl,
          y,Fin.append_right,gammaPointCode,Fin.append_left,Y,vfAt]
      | right i => exact i.elim0
  change (∃ w : Fin (1+m) → M,
    Sum.elim (Fin.append (gammaPointCode s) (gammaPointCode z)) w ∘ σQ ∈ GammaTupleGraphs.rawGraph rQ ∧
    Sum.elim (Fin.append (gammaPointCode s) (gammaPointCode z)) w ∘ σg ∈ GammaTupleGraphs.rawGraph rg ∧
    w (Fin.castAdd m 0) = Fin.append (gammaPointCode s) (gammaPointCode z) x) ↔ _
  have hX : Fin.append (gammaPointCode s) (gammaPointCode z) x = (vfAt z 0).val := by
    simp only [x,Fin.append_right,gammaPointCode,Fin.append_left]
  simp_rw [hQtuple,hGtuple]
  simp only [hX]
  constructor
  · rintro ⟨w,hqw,hgw,hw⟩
    obtain ⟨p,hp,u,hu,hQu⟩ := (GammaTupleGraphs.rawGraph_left_iff rQ w s).mp hqw
    obtain ⟨p',hp',v,hv,hgv⟩ := (GammaTupleGraphs.rawGraph_left_iff rg w Y).mp hgw
    have huv : u = v := by
      apply Subtype.ext
      apply GammaTupleGraphs.code_injective
      exact (congrArg gammaPointCode hu).trans (hp.trans (hp'.symm.trans (congrArg gammaPointCode hv).symm))
    subst v
    have hCode := (congrArg gammaPointCode hu).trans hp
    have hFirst : vfAt u.val 0 = vfAt z 0 := by
      apply Subtype.ext
      have hh := congrFun hCode (Fin.castAdd m (0 : Fin 1))
      have he : (vfAt u.val 0).val = w (Fin.castAdd m 0) := by
        simpa only [gammaPointCode,Fin.append_left] using hh
      exact he.trans hw
    exact ⟨u,hQu,hFirst,hgv⟩
  · rintro ⟨u,hQu,hFirst,hgu⟩
    refine ⟨gammaPointCode u.val,⟨u.val,s,⟨u,rfl,hQu⟩,rfl⟩,
      ⟨u.val,Y,⟨u,rfl,hgu⟩,rfl⟩,?_⟩
    simpa only [gammaPointCode,Fin.append_left] using congrArg Subtype.val hFirst

end IntegrationInACVF.Section4.UniformPositionGraphs
