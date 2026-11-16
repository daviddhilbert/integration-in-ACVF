module

public import Section5.GammaInvariantLogic
public import Section3.GammaFullDescent

@[expose] public section

/-! Realize native Gamma sets and complete graphs over the fixed common
real names of their original base. This exposes the fixed-name version of
the private flattening argument in pinned Special transformations,
Section5/GammaInvariantLogic.lean (9cc9760892092dd34cfad4a6dee655843c52f30c).
The native geometry and the mathematical Gamma base are unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)

private structure NativeSortedView (P : PresentedSpace (M := M)) where
  arity : ℕ
  sort : Fin arity → SortTag
  index : @SpecialTransformations.DefinableGeometry.Space.Index LRV M N P ≃ Fin arity
  code : Carrier P → Fin arity → M
  domain_iff : ∀ z : Fin arity → M, z ∘ index ∈ pDomain P ↔ ∀ i, sortEval (sort i) (z i)
  code_decode : ∀ c : pDomain P, code (pDecode P c) = c.val ∘ index.symm

namespace NativeSortedView

variable {P Q : PresentedSpace (M := M)}

private def point (n m : ℕ) : NativeSortedView (pointSpace (M := M) n m) where
  arity := n + m
  sort := gammaPointSort n m
  index := finSumFinEquiv
  code := gammaPointCode
  domain_iff z := by
    constructor
    · rintro ⟨hx, hy⟩ i
      cases i using Fin.addCases with
      | left i => simpa only [gammaPointSort, Fin.append_left, Function.comp_apply,
          finSumFinEquiv_apply_left] using hx i
      | right i => simpa only [gammaPointSort, Fin.append_right, Function.comp_apply,
          finSumFinEquiv_apply_right] using hy i
    · intro h
      exact ⟨fun i => by simpa only [gammaPointSort, Fin.append_left, Function.comp_apply,
          finSumFinEquiv_apply_left] using h (Fin.castAdd m i),
        fun i => by simpa only [gammaPointSort, Fin.append_right, Function.comp_apply,
          finSumFinEquiv_apply_right] using h (Fin.natAdd n i)⟩
  code_decode c := by
    funext i
    cases i using Fin.addCases with
    | left i => simp only [gammaPointCode, vfAt, Fin.append_left, Function.comp_apply,
        finSumFinEquiv_symm_apply_castAdd]
    | right i => simp only [gammaPointCode, Fin.append_right, Function.comp_apply,
        finSumFinEquiv_symm_apply_natAdd]

private def prod (F : NativeSortedView P) (G : NativeSortedView Q) : NativeSortedView (spaceProd P Q) where
  arity := F.arity + G.arity
  sort := Fin.append F.sort G.sort
  index := (Equiv.sumCongr F.index G.index).trans finSumFinEquiv
  code x := Fin.append (F.code x.1) (G.code x.2)
  domain_iff z := by
    change (((z ∘ Fin.castAdd G.arity) ∘ F.index) ∈ pDomain P ∧
      ((z ∘ Fin.natAdd F.arity) ∘ G.index) ∈ pDomain Q) ↔ _
    rw [F.domain_iff (z ∘ Fin.castAdd G.arity), G.domain_iff (z ∘ Fin.natAdd F.arity)]
    constructor
    · rintro ⟨hx, hy⟩ i
      cases i using Fin.addCases with
      | left i => simpa only [Fin.append_left, Function.comp_apply] using hx i
      | right i => simpa only [Fin.append_right, Function.comp_apply] using hy i
    · intro h
      exact ⟨fun i => by simpa only [Fin.append_left, Function.comp_apply] using h (Fin.castAdd G.arity i),
        fun i => by simpa only [Fin.append_right, Function.comp_apply] using h (Fin.natAdd F.arity i)⟩
  code_decode c := by
    change Fin.append (F.code (pDecode P ⟨c.val ∘ Sum.inl, c.property.1⟩))
      (G.code (pDecode Q ⟨c.val ∘ Sum.inr, c.property.2⟩)) = _
    rw [F.code_decode, G.code_decode]
    funext i
    cases i using Fin.addCases with
    | left i =>
      rw [Fin.append_left]
      change c.val (Sum.inl (F.index.symm i)) =
        c.val ((Equiv.sumCongr F.index G.index).symm (finSumFinEquiv.symm (Fin.castAdd G.arity i)))
      rw [finSumFinEquiv_symm_apply_castAdd] <;> rfl
    | right i =>
      rw [Fin.append_right]
      change c.val (Sum.inr (G.index.symm i)) =
        c.val ((Equiv.sumCongr F.index G.index).symm (finSumFinEquiv.symm (Fin.natAdd F.arity i)))
      rw [finSumFinEquiv_symm_apply_natAdd] <;> rfl

private theorem code_sorted (F : NativeSortedView P) (x : Carrier P) :
    ∀ i, sortEval (F.sort i) (F.code x i) := by
  obtain ⟨c, rfl⟩ := (@SpecialTransformations.DefinableGeometry.Space.onto LRV M N P) x
  rw [F.code_decode, ← F.domain_iff]
  have he : (c.val ∘ F.index.symm) ∘ F.index = c.val :=
    funext fun i => congrArg c.val (F.index.symm_apply_apply i)
  exact he.symm ▸ c.property

private theorem code_injective (F : NativeSortedView P) : Function.Injective F.code := by
  intro x y h
  obtain ⟨c, rfl⟩ := (@SpecialTransformations.DefinableGeometry.Space.onto LRV M N P) x
  obtain ⟨d, rfl⟩ := (@SpecialTransformations.DefinableGeometry.Space.onto LRV M N P) y
  rw [F.code_decode, F.code_decode] at h
  exact congrArg (pDecode P) (Subtype.ext (funext fun i => by
    simpa only [Function.comp_apply, F.index.symm_apply_apply] using congrFun h (F.index i)))

private theorem real_of_flat (F : NativeSortedView P) {S : Set M} {A : Set (Carrier P)}
    (hA : DefinableOver S F.sort (F.code '' A)) : SetDefinable P S A := by
  have hraw := (definableOver_iff_normalized_raw S F.sort _).mp hA
  have h := @Set.Definable.preimage_comp M S LRV N _ _ F.index.symm _ hraw.1
  change @Set.Definable M S LRV N _ (@SpecialTransformations.DefinableGeometry.Space.preimage LRV M N P A)
  convert h using 1
  ext z
  constructor
  · rintro ⟨hz, ha⟩
    exact ⟨pDecode P ⟨z, hz⟩, ha, F.code_decode ⟨z, hz⟩⟩
  · rintro ⟨a, ha, he⟩
    change F.code a = z ∘ F.index.symm at he
    have hz : z ∈ pDomain P := by
      have hh := (F.domain_iff (z ∘ F.index.symm)).mpr (he ▸ F.code_sorted a)
      have he' : (z ∘ F.index.symm) ∘ F.index = z :=
        funext fun i => congrArg z (F.index.symm_apply_apply i)
      exact he' ▸ hh
    refine ⟨hz, ?_⟩
    change pDecode P ⟨z, hz⟩ ∈ A
    have he' := F.code_injective ((F.code_decode ⟨z, hz⟩).trans he.symm)
    exact he'.symm ▸ ha

private def vf (n : ℕ) : NativeSortedView (@SpecialTransformations.Section4.vfSpace M sM hM n) where
  arity := n
  sort := fun _ => .vf
  index := Equiv.refl _
  code p := fun i => (p i).val
  domain_iff _ := Iff.rfl
  code_decode _ := rfl

end NativeSortedView

variable {B : Base (M := M)} {n m u w : ℕ}

theorem gamma_native_set_common_names {A : Set (Point (M := M) n m)}
    (hA : GammaSetDefinable B A) :
    SetDefinable (pointSpace n m) (commonRealNames B) A :=
  (NativeSortedView.point n m).real_of_flat hA.common_names

theorem gamma_native_graph_common_names
    {r : Point (M := M) n m → Point (M := M) u w → Prop}
    (hr : GammaGraphDefinable B r) :
    RelationDefinable (pointSpace n m) (pointSpace u w) (commonRealNames B) r := by
  let F := (NativeSortedView.point (M := M) n m).prod (NativeSortedView.point u w)
  have he : F.code '' {p | r p.1 p.2} =
      {z | ∃ p q, r p q ∧ Fin.append (gammaPointCode p) (gammaPointCode q) = z} := by
    ext z
    constructor
    · rintro ⟨⟨p,q⟩,hpq,rfl⟩
      exact ⟨p,q,hpq,rfl⟩
    · rintro ⟨p,q,hpq,rfl⟩
      exact ⟨(p,q),hpq,rfl⟩
  have h : DefinableOver (commonRealNames B) F.sort (F.code '' {p | r p.1 p.2}) := by
    rw [he]
    exact hr.common_names
  exact (@SpecialTransformations.DefinableGeometry.Space.definable_prod_iff LRV M N
    (pointSpace n m) (pointSpace u w) _ r).mp (F.real_of_flat h)

theorem gamma_native_scalar_common_names
    {r : Point (M := M) n m → VF (M := M) → Prop}
    (hr : GammaScalarGraphDefinable B r) :
    RelationDefinable (pointSpace n m) (SpecialTransformations.Section4.vfSpace 1)
      (commonRealNames B) (fun p z => r p (z 0)) := by
  let F := (NativeSortedView.point (M := M) n m).prod (NativeSortedView.vf 1)
  have he : F.code '' {p | r p.1 (p.2 0)} =
      {z | ∃ p : Point (M := M) n m, ∃ q : Point (M := M) 1 0,
        r p (vfAt q 0) ∧ Fin.append (gammaPointCode p) (gammaPointCode q) = z} := by
    ext z
    constructor
    · rintro ⟨⟨p,q⟩,hpq,rfl⟩
      refine ⟨p,(q,Fin.elim0),hpq,?_⟩
      apply congrArg (Fin.append (gammaPointCode p))
      funext i
      fin_cases i
      rfl
    · rintro ⟨p,q,hpq,rfl⟩
      refine ⟨(p,q.1),hpq,?_⟩
      apply congrArg (Fin.append (gammaPointCode p))
      funext i
      fin_cases i
      rfl
  have h : DefinableOver (commonRealNames B) F.sort (F.code '' {p | r p.1 (p.2 0)}) := by
    rw [he]
    have hsort : gammaPointSort 1 0 = (fun _ : Fin 1 => SortTag.vf) := by
      funext i
      fin_cases i
      rfl
    have h := hr.common_names
    change DefinableOver (commonRealNames B)
      (Fin.append (gammaPointSort n m) (gammaPointSort 1 0)) _ at h
    rw [hsort] at h
    exact h
  exact (@SpecialTransformations.DefinableGeometry.Space.definable_prod_iff LRV M N
    (pointSpace n m) (SpecialTransformations.Section4.vfSpace 1) _
    (fun p z => r p (z 0))).mp (F.real_of_flat h)

end IntegrationInACVF.Section7
