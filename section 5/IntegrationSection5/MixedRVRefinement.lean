import IntegrationSection5.MixedScalarFamilies

/-! Descend actual mixed scalar-family refinement graphs to finite RV maps
on the original mixed source. Complementary VF parameters remain free. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5.MixedScalarFamilies
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {p m d : ℕ}

def fromRefinement (G : GammaParameters.Base (M := M))
    (C : (Fin (p+m) → M) → Set M) (e : (Fin (p+m) → M) → M → Fin d → M)
    (he : FamilyPositionRefinement.RVRefinement (GammaBaseBridge.fullBase G) C e) :
    GammaRVMap G (domain (p := p) (m := m) C) d where
  toFun a i := ⟨e (context a.val) (vfAt a.val 0).val i,he.1 _ _ a.property i⟩
  graph := by
    let ι := Fin (((p+1)+m)+(0+d))
    let key (i : Fin (p+m)) : ι := Fin.castAdd (0+d) (contextIndex p m i)
    let x : ι := Fin.castAdd (0+d) (Fin.castAdd m (0 : Fin (p+1)))
    let out (i : Fin d) : ι := Fin.natAdd ((p+1)+m) (Fin.natAdd 0 i)
    let ρ : (Fin (p+m) ⊕ Fin 1) ⊕ Fin d → ι := Sum.elim (Sum.elim key (fun _ => x)) out
    have h := GammaTupleGraphs.relation_of_full G _ (FullBaseAtomicity.OverBase.preimage_comp he.2 ρ)
    apply GammaGraphDefinable.congr h
    intro a b
    have hc : (fun i => Fin.append (gammaPointCode a) (gammaPointCode b) (key i)) = context a := by
      funext i
      exact (Fin.append_left _ _ _).trans (context_code a i)
    have hx : Fin.append (gammaPointCode a) (gammaPointCode b) x = (vfAt a 0).val := by
      simp only [x,Fin.append_left,gammaPointCode]
    have ho : (fun i => Fin.append (gammaPointCode a) (gammaPointCode b) (out i)) =
        fun i => (b.2 i).val := by
      funext i
      simp only [out,Fin.append_right,gammaPointCode]
    change ((Fin.append (gammaPointCode a) (gammaPointCode b) x) ∈
      C (fun i => Fin.append (gammaPointCode a) (gammaPointCode b) (key i)) ∧
      (fun i => Fin.append (gammaPointCode a) (gammaPointCode b) (out i)) =
        e (fun i => Fin.append (gammaPointCode a) (gammaPointCode b) (key i))
          (Fin.append (gammaPointCode a) (gammaPointCode b) x)) ↔ _
    rw [hc,hx,ho]
    constructor
    · rintro ⟨ha,hb⟩
      refine ⟨⟨a,ha⟩,rfl,funext fun i => ?_⟩
      exact Subtype.ext (congrFun hb i).symm
    · rintro ⟨c,rfl,hvalues⟩
      refine ⟨c.property,funext fun i => ?_⟩
      exact (congrArg Subtype.val (congrFun hvalues i)).symm

theorem fromRefinement_values (G : GammaParameters.Base (M := M))
    (C : (Fin (p+m) → M) → Set M) (e : (Fin (p+m) → M) → M → Fin d → M)
    (he : FamilyPositionRefinement.RVRefinement (GammaBaseBridge.fullBase G) C e)
    (a : domain (p := p) (m := m) C) :
    (fun i => ((fromRefinement G C e he).toFun a i).val) = e (context a.val) (vfAt a.val 0).val := rfl

end IntegrationInACVF.Section5.MixedScalarFamilies
