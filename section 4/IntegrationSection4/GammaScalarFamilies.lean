import IntegrationSection4.GammaFamilySyntax

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.GammaScalarFamilies

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {m : ℕ}

def family (D : Set (Point (M := M) 1 m)) (p : Fin m → M) : Set M :=
  {x | ∃ a : D, GammaFamilySyntax.labels a.val = p ∧ (vfAt a.val 0).val = x}

theorem point_unique {D : Set (Point (M := M) 1 m)} {a b : D}
    (hp : GammaFamilySyntax.labels a.val = GammaFamilySyntax.labels b.val)
    (hx : (vfAt a.val 0).val = (vfAt b.val 0).val) : a = b := by
  apply Subtype.ext
  apply Prod.ext
  · funext i
    fin_cases i
    exact Subtype.ext hx
  · funext i
    exact Subtype.ext (congrFun hp i)

def value {D : Set (Point (M := M) 1 m)} (g : D → VF (M := M))
    (p : Fin m → M) (x : M) : M :=
  if h : x ∈ family D p then (g (Classical.choose h)).val else iVFZero

theorem value_on {D : Set (Point (M := M) 1 m)} (g : D → VF (M := M)) (a : D) :
    value g (GammaFamilySyntax.labels a.val) (vfAt a.val 0).val = (g a).val := by
  have ha : (vfAt a.val 0).val ∈ family D (GammaFamilySyntax.labels a.val) := ⟨a,rfl,rfl⟩
  rw [value,dif_pos ha]
  have hh : Classical.choose ha = a := point_unique (Classical.choose_spec ha).1 (Classical.choose_spec ha).2
  rw [hh]

theorem domain_eq (D : Set (Point (M := M) 1 m)) :
    GammaFamilySyntax.domain (family D) = D := by
  ext p
  constructor
  · rintro ⟨a,hl,hx⟩
    have he : a.val = p := by
      apply Prod.ext
      · funext i; fin_cases i; exact Subtype.ext hx
      · funext i; exact Subtype.ext (congrFun hl i)
    exact he ▸ a.property
  · intro hp
    exact ⟨⟨p,hp⟩,rfl,rfl⟩

/-- Convert an actual original-base mixed scalar function into the raw
family interface, making invalid sort contexts empty. No parameters are added. -/
theorem graph_definable (G : GammaParameters.Base (M := M))
    (D : Set (Point (M := M) 1 m)) (g : D → VF (M := M))
    (hg : GammaScalarGraphDefinable G (fun p y => ∃ a : D, a.val = p ∧ g a = y)) :
    FiniteScalarFamilies.Graph (GammaBaseBridge.fullBase G) (family D) (value g) := by
  let B := GammaBaseBridge.fullBase G
  have hFull := GammaBaseBridge.of_gamma G hg
  let ι := (Fin m ⊕ Fin 1) ⊕ Fin 1
  let ρ : Fin ((1+m)+(1+0)) → ι := Fin.addCases
    (Fin.addCases (fun _ : Fin 1 => .inl (.inr 0)) (fun i : Fin m => .inl (.inl i)))
    (Fin.addCases (fun _ : Fin 1 => .inr 0) (fun i : Fin 0 => i.elim0))
  have hPull := FullBaseAtomicity.OverBase.preimage_comp hFull ρ
  apply FullBaseAtomicity.OverBase.congr hPull
  intro z
  change (∃ (p : Point (M := M) 1 m) (q : Point (M := M) 1 0),
    (∃ a : D, a.val = p ∧ g a = vfAt q 0) ∧
      Fin.append (gammaPointCode p) (gammaPointCode q) = z ∘ ρ) ↔
    z (.inl (.inr 0)) ∈ family D (z ∘ Sum.inl ∘ Sum.inl) ∧
      z (.inr 0) = value g (z ∘ Sum.inl ∘ Sum.inl) (z (.inl (.inr 0)))
  constructor
  · rintro ⟨p,q,⟨a,rfl,hg⟩,he⟩
    have hx : (vfAt a.val 0).val = z (.inl (.inr 0)) := by
      have hh := congrFun he (Fin.castAdd (1+0) (Fin.castAdd m (0 : Fin 1)))
      simpa only [Fin.append_left,gammaPointCode,Fin.append_left,Function.comp_apply,ρ,Fin.addCases_left] using hh
    have hp : GammaFamilySyntax.labels a.val = z ∘ Sum.inl ∘ Sum.inl := by
      funext i
      have hh := congrFun he (Fin.castAdd (1+0) (Fin.natAdd 1 i))
      simpa only [GammaFamilySyntax.labels,Fin.append_left,gammaPointCode,Fin.append_right,Function.comp_apply,ρ,Fin.addCases_left,Fin.addCases_right] using hh
    have hy : (vfAt q 0).val = z (.inr 0) := by
      have hh := congrFun he (Fin.natAdd (1+m) (Fin.castAdd 0 (0 : Fin 1)))
      simpa only [Fin.append_right,gammaPointCode,Fin.append_left,Function.comp_apply,ρ,Fin.addCases_left,Fin.addCases_right] using hh
    refine ⟨⟨a,hp,hx⟩,?_⟩
    rw [← hp,← hx,value_on]
    exact hy.symm.trans (congrArg Subtype.val hg).symm
  · rintro ⟨hx,hy⟩
    obtain ⟨a,hp,ha⟩ := hx
    have hv : value g (z ∘ Sum.inl ∘ Sum.inl) (z (.inl (.inr 0))) = (g a).val := by
      rw [← hp,← ha,value_on]
    have hz : z (.inr 0) = (g a).val := hy.trans hv
    let q : Point (M := M) 1 0 := (fun _ => g a,Fin.elim0)
    refine ⟨a.val,q,⟨a,rfl,rfl⟩,?_⟩
    funext i
    cases i using Fin.addCases with
    | left i =>
      cases i using Fin.addCases with
      | left i =>
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simpa only [Fin.append_left,gammaPointCode,Fin.append_left,Function.comp_apply,ρ,Fin.addCases_left,vfAt] using ha
      | right i =>
        simpa only [GammaFamilySyntax.labels,Fin.append_left,gammaPointCode,Fin.append_right,Function.comp_apply,ρ,Fin.addCases_left,Fin.addCases_right] using congrFun hp i
    | right i =>
      cases i using Fin.addCases with
      | left i =>
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simpa only [q,Fin.append_right,gammaPointCode,Fin.append_left,Function.comp_apply,ρ,Fin.addCases_left,Fin.addCases_right,vfAt] using hz.symm
      | right i => exact i.elim0

theorem domain_vf (D : Set (Point (M := M) 1 m)) (p : Fin m → M) :
    family D p ⊆ {x | iVF x} := by
  rintro x ⟨a,_,hx⟩
  exact hx ▸ (vfAt a.val 0).property

theorem value_vf {D : Set (Point (M := M) 1 m)} (g : D → VF (M := M))
    (p : Fin m → M) (x : M) (hx : x ∈ family D p) : iVF (value g p x) := by
  rw [value,dif_pos hx]
  exact (g (Classical.choose hx)).property

end IntegrationInACVF.Section4.GammaScalarFamilies
