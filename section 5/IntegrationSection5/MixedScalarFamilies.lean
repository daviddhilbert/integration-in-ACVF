import IntegrationSection4.GammaRVMapOperations
import IntegrationSection4.GammaScalarFamilies
import IntegrationSection5.GammaGraphOperations

/-! Uniform scalar families with complementary VF coordinates and old RV
labels both retained as free parameters over the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open SpecialTransformations.Milestone0.Transfer
open IntegrationInACVF.Section3ACVF
namespace IntegrationInACVF.Section5.MixedScalarFamilies
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {p m : ℕ}

def context (a : Point (M := M) (p+1) m) : Fin (p+m) → M := gammaPointCode (dropHead id a)

def family (D : Set (Point (M := M) (p+1) m)) (c : Fin (p+m) → M) : Set M :=
  {x | ∃ a : D, context a.val = c ∧ (vfAt a.val 0).val = x}

theorem point_unique {D : Set (Point (M := M) (p+1) m)} {a b : D}
    (hc : context a.val = context b.val) (hx : (vfAt a.val 0).val = (vfAt b.val 0).val) : a = b := by
  have htail := IntegrationInACVF.Section5.gammaPointCode_injective hc
  apply Subtype.ext
  refine Prod.ext ?_ (congrArg (fun q : Point (M := M) p m => q.2) htail)
  funext j
  cases j using Fin.cases with
  | zero => exact Subtype.ext hx
  | succ j => exact congrArg (fun q : Point (M := M) p m => vfAt q j) htail

def value {D : Set (Point (M := M) (p+1) m)} (g : D → VF (M := M))
    (c : Fin (p+m) → M) (x : M) : M :=
  if h : x ∈ family D c then (g (Classical.choose h)).val else iVFZero

theorem value_on {D : Set (Point (M := M) (p+1) m)} (g : D → VF (M := M)) (a : D) :
    value g (context a.val) (vfAt a.val 0).val = (g a).val := by
  have ha : (vfAt a.val 0).val ∈ family D (context a.val) := ⟨a,rfl,rfl⟩
  rw [value,dif_pos ha]
  have he : Classical.choose ha = a := point_unique (Classical.choose_spec ha).1 (Classical.choose_spec ha).2
  rw [he]

def domain (C : (Fin (p+m) → M) → Set M) : Set (Point (M := M) (p+1) m) :=
  {a | (vfAt a 0).val ∈ C (context a)}

theorem domain_family (D : Set (Point (M := M) (p+1) m)) : domain (family D) = D := by
  ext a
  constructor
  · rintro ⟨b,hc,hx⟩
    have he : b.val = a := by
      have htail := IntegrationInACVF.Section5.gammaPointCode_injective hc
      refine Prod.ext ?_ (congrArg (fun q : Point (M := M) p m => q.2) htail)
      funext j
      cases j using Fin.cases with
      | zero => exact Subtype.ext hx
      | succ j => exact congrArg (fun q : Point (M := M) p m => vfAt q j) htail
    exact he ▸ b.property
  · intro ha
    exact ⟨⟨a,ha⟩,rfl,rfl⟩

def contextIndex (p m : ℕ) : Fin (p+m) → Fin ((p+1)+m) :=
  Fin.addCases (fun i => Fin.castAdd m i.succ) (Fin.natAdd (p+1))

theorem context_code (a : Point (M := M) (p+1) m) (i : Fin (p+m)) :
    gammaPointCode a (contextIndex p m i) = context a i := by
  cases i using Fin.addCases with
  | left i => simp only [contextIndex,Fin.addCases_left,gammaPointCode,context,Fin.append_left]; rfl
  | right i => simp only [contextIndex,Fin.addCases_right,gammaPointCode,context,Fin.append_right]; rfl

theorem domain_vf (D : Set (Point (M := M) (p+1) m)) (c : Fin (p+m) → M) :
    family D c ⊆ {x | iVF x} := by
  rintro x ⟨a,_,hx⟩
  exact hx ▸ (vfAt a.val 0).property

theorem value_vf {D : Set (Point (M := M) (p+1) m)} (g : D → VF (M := M))
    (c : Fin (p+m) → M) (x : M) (hx : x ∈ family D c) : iVF (value g c x) := by
  rw [value,dif_pos hx]
  exact (g (Classical.choose hx)).property

theorem graph_definable (G : GammaParameters.Base (M := M))
    (D : Set (Point (M := M) (p+1) m)) (g : D → VF (M := M))
    (hg : GammaScalarGraphDefinable G (fun a y => ∃ b : D, b.val = a ∧ g b = y)) :
    IntegrationInACVF.Section4.FiniteScalarFamilies.Graph
      (IntegrationInACVF.Section4.GammaBaseBridge.fullBase G) (family D) (value g) := by
  let ι := (Fin (p+m) ⊕ Fin 1) ⊕ Fin 1
  let ρ : Fin (((p+1)+m)+(1+0)) → ι := Fin.addCases
    (Fin.addCases (Fin.cases (.inl (.inr 0)) (fun i => .inl (.inl (Fin.castAdd m i))))
      (fun i => .inl (.inl (Fin.natAdd p i))))
    (Fin.addCases (fun _ : Fin 1 => .inr 0) (fun i : Fin 0 => i.elim0))
  have h := FullBaseAtomicity.OverBase.preimage_comp
    (IntegrationInACVF.Section4.GammaBaseBridge.of_gamma G hg) ρ
  apply FullBaseAtomicity.OverBase.congr h
  intro z
  change (∃ (a : Point (M := M) (p+1) m) (b : Point (M := M) 1 0),
    (∃ c : D, c.val = a ∧ g c = vfAt b 0) ∧
      Fin.append (gammaPointCode a) (gammaPointCode b) = z ∘ ρ) ↔ _
  constructor
  · rintro ⟨a,b,⟨c,rfl,hg⟩,he⟩
    have hx : (vfAt c.val 0).val = z (.inl (.inr 0)) := by
      have h := congrFun he (Fin.castAdd (1+0) (Fin.castAdd m (0 : Fin (p+1))))
      simpa only [Fin.append_left,gammaPointCode,Function.comp_apply,ρ,Fin.addCases_left,Fin.cases_zero] using h
    have hc : context c.val = z ∘ Sum.inl ∘ Sum.inl := by
      funext i
      have h := congrFun he (Fin.castAdd (1+0) (contextIndex p m i))
      rw [Fin.append_left,context_code] at h
      cases i using Fin.addCases with
      | left i => simpa only [Function.comp_apply,ρ,contextIndex,Fin.addCases_left,Fin.cases_succ] using h
      | right i => simpa only [Function.comp_apply,ρ,contextIndex,Fin.addCases_left,Fin.addCases_right] using h
    have hy : (vfAt b 0).val = z (.inr 0) := by
      have h := congrFun he (Fin.natAdd ((p+1)+m) (Fin.castAdd 0 (0 : Fin 1)))
      simpa only [Fin.append_right,gammaPointCode,Fin.append_left,Function.comp_apply,ρ,Fin.addCases_right,Fin.addCases_left] using h
    refine ⟨⟨c,hc,hx⟩,?_⟩
    rw [← hc,← hx,value_on]
    exact hy.symm.trans (congrArg Subtype.val hg).symm
  · rintro ⟨⟨a,hc,hx⟩,hy⟩
    have hv : value g (z ∘ Sum.inl ∘ Sum.inl) (z (.inl (.inr 0))) = (g a).val := by
      rw [← hc,← hx,value_on]
    have hz : z (.inr 0) = (g a).val := hy.trans hv
    let b : Point (M := M) 1 0 := (fun _ => g a,Fin.elim0)
    refine ⟨a.val,b,⟨a,rfl,rfl⟩,?_⟩
    funext i
    cases i using Fin.addCases with
    | left i =>
      cases i using Fin.addCases with
      | left i =>
        cases i using Fin.cases with
        | zero => simpa only [Fin.append_left,gammaPointCode,Function.comp_apply,ρ,Fin.addCases_left,Fin.cases_zero] using hx
        | succ i =>
          have h := congrFun hc (Fin.castAdd m i)
          simpa only [context,Fin.append_left,gammaPointCode,Function.comp_apply,ρ,Fin.addCases_left,Fin.cases_succ,dropHead,vfAt] using h
      | right i =>
        have h := congrFun hc (Fin.natAdd p i)
        simpa only [context,Fin.append_right,gammaPointCode,Fin.append_left,Function.comp_apply,ρ,Fin.addCases_left,Fin.addCases_right,dropHead,id_eq] using h
    | right i =>
      cases i using Fin.addCases with
      | left i =>
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simpa only [b,Fin.append_right,gammaPointCode,Fin.append_left,Function.comp_apply,ρ,Fin.addCases_left,Fin.addCases_right,vfAt] using hz.symm
      | right i => exact i.elim0

end IntegrationInACVF.Section5.MixedScalarFamilies
