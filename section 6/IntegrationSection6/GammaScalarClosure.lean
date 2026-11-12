import Section5.GammaLogic
import Section3.GammaRealMap
import Section3.GammaBaseVFAlgebraicity

/-! A scalar function with a full original-Gamma graph is VF-algebraic
over the real base and its VF inputs. Arbitrary RV and Gamma names do not
enlarge the VF algebraic closure; no small presentation-code set is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

private theorem gammaPointCode_injective :
    Function.Injective (gammaPointCode (M := M) (n := n) (m := m)) := by
  intro p q he
  apply Prod.ext
  · funext i
    apply Subtype.ext
    simpa only [gammaPointCode,Fin.append_left,vfAt] using congrFun he (Fin.castAdd m i)
  · funext i
    apply Subtype.ext
    simpa only [gammaPointCode,Fin.append_right] using congrFun he (Fin.natAdd n i)

theorem gamma_scalar_value_algebraic {D : Set (Point (M := M) n m)}
    (g : D → VF (M := M))
    (hg : GammaScalarGraphDefinable B (fun p y => ∃ a : D, a.val = p ∧ g a = y))
    (a : D) : AlgebraicAt (B.real ∪ Set.range (fun i => (a.val.1 i).val)) .vf (g a).val := by
  let R := Set.range (fun i => (a.val.2 i).val)
  let S0 := B.real ∪ Set.range (fun i => (a.val.1 i).val)
  let H : Base (M := M) := ⟨S0 ∪ R,B.gamma⟩
  have hgH : GammaScalarGraphDefinable H (fun p y => ∃ a : D, a.val = p ∧ g a = y) :=
    DefinableOverBase.mono hg (fun _ h => Or.inl (Or.inl h)) (Set.Subset.refl _)
  let c := gammaPointCode a.val
  let F (z : Fin 1 → M) : Fin ((n+m)+(1+0)) → M := Fin.append c z
  have hF : @Set.DefinableMap M LRV N (Fin 1) (Fin ((n+m)+(1+0))) H.real F := by
    intro j
    cases j using Fin.addCases with
    | left j =>
      simp only [F,Fin.append_left]
      change @Set.DefinableFun M LRV N (Fin 1) H.real (fun _ => c j)
      letI := N
      apply LRV.definableFun_const
      cases j using Fin.addCases with
      | left j =>
        apply Or.inl
        apply Or.inr
        refine ⟨j,?_⟩
        simp only [c,gammaPointCode,Fin.append_left,vfAt]
      | right j =>
        apply Or.inr
        refine ⟨j,?_⟩
        simp only [c,gammaPointCode,Fin.append_right]
    | right j =>
      simp only [F,Fin.append_right]
      exact @Set.DefinableFun.proj M LRV N (Fin 1) H.real j
  have hd := DefinableOverBase.preimage_real_map hgH (fun _ : Fin 1 => SortTag.vf) F hF
  have hsingle : DefinableAtBase H .vf {(g a).val} := by
    change DefinableOverBase H (fun _ : Fin 1 => .vf) {z | z 0 ∈ ({(g a).val} : Set M)}
    convert hd using 1
    ext z
    constructor
    · intro hz
      change z 0 = (g a).val at hz
      let q : Point (M := M) 1 0 := (fun _ => g a,Fin.elim0)
      refine ⟨⟨a.val,q,⟨a,rfl,rfl⟩,?_⟩,?_⟩
      · apply congrArg (Fin.append (gammaPointCode a.val))
        funext j
        fin_cases j
        exact hz.symm
      · intro j
        fin_cases j
        change sortEval .vf (z 0)
        rw [hz]
        exact (g a).property
    · rintro ⟨⟨p,q,⟨b,hb,hg⟩,hcode⟩,_⟩
      have hp : p = a.val := gammaPointCode_injective (funext (fun j => by
        simpa only [F,Fin.append_left] using congrFun hcode (Fin.castAdd (1+0) j)))
      have hba : b = a := Subtype.ext (hb.trans hp)
      have hq : (vfAt q 0).val = z 0 := by
        have ht0 : gammaPointCode q (0 : Fin (1+0)) = z 0 := by
          simpa only [F,Fin.append_right] using
            congrFun hcode (Fin.natAdd (n+m) (0 : Fin (1+0)))
        have hi : (0 : Fin (1+0)) = Fin.castAdd 0 (0 : Fin 1) := Fin.ext rfl
        have ht := (congrArg (gammaPointCode q) hi).symm.trans ht0
        simpa only [gammaPointCode,Fin.append_left,vfAt] using ht
      change z 0 = (g a).val
      exact hq.symm.trans ((congrArg Subtype.val hg).symm.trans (congrArg (fun b => (g b).val) hba))
  have ha : AlgebraicAtBase H .vf (g a).val := ⟨{(g a).val},hsingle,Set.finite_singleton _,Set.mem_singleton _⟩
  have hr := (algebraic_vf_iff_real H (g a)).mp ha
  exact (algebraicAt_vf_union_rv_iff S0 R (by
    rintro t ⟨i,rfl⟩
    exact (a.val.2 i).property) (g a)).mp hr

end IntegrationInACVF.Section6
