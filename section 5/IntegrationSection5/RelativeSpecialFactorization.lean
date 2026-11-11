import IntegrationSection5.RelativeSpecialChain

/-! The actual canonical map, and hence every special bijection, is a finite
composition of relatively special bijections. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ}

theorem canonical_relativeSpecial_factorization (A : DefSet (M := M) S n m) :
    ∃ t : RelativeSpecialChain S n A (canonicalImage A),
      t.toMap = (SpecialBijection.canonical A).toMap := by
  obtain ⟨r,B,t,hr,ht⟩ := coordinateCanonical_sequence A (List.ofFn (id : Fin n → Fin n)).reverse
  have hArity : r = n+m := by simpa using hr
  clear hr
  subst r
  have htval : ∀ a : A, (t.toMap a).val = canonical a.val := by
    intro a
    obtain ⟨hv,hlabels⟩ := ht a
    refine Prod.ext hv (List.ofFn_injective ?_)
    change pointRVList (t.toMap a).val = List.ofFn (Fin.append (fun i => @rv M sM hM (vfAt a.val i)) a.val.2)
    simpa only [List.reverse_reverse,List.map_ofFn,Function.comp_id,List.ofFn_fin_append,pointRVList] using hlabels
  have hBC : B = canonicalImage A := by
    cases hB : B with
    | mk X hXd =>
      cases hC : canonicalImage A with
      | mk Y hYd =>
        have hXY : X = Y := by
          have hset : carrier B = carrier (canonicalImage A) := by
            ext q
            constructor
            · intro hq
              obtain ⟨a,ha⟩ := t.bijective.2 ⟨q,hq⟩
              refine ⟨a,?_⟩
              exact (htval a).symm.trans (congrArg Subtype.val ha)
            · rintro ⟨a,ha⟩
              have he : (t.toMap a).val = q := (htval a).trans ha
              exact he ▸ (t.toMap a).property
          simpa only [hB,hC] using hset
        subst Y
        rfl
  refine ⟨t.castTarget hBC,?_⟩
  apply Map.ext
  intro a
  apply Subtype.ext
  rw [RelativeSpecialChain.castTarget_val]
  exact htval a

theorem primitive_relativeSpecial_factorization {A : DefSet (M := M) S n m}
    {B : DefSet (M := M) S n l} (p : Primitive S n A B) :
    ∃ t : RelativeSpecialChain S n A B, t.toMap = p.toMap := by
  cases p with
  | canonical A => exact canonical_relativeSpecial_factorization A
  | @centripetal m i k D =>
    refine ⟨.cons i (SpecialBijection.centripetal D).toMap
      (SpecialBijection.centripetal D).bijective (centripetal_specialRelative D) (.nil _),?_⟩
    apply Map.ext
    intro a
    rfl

theorem chain_relativeSpecial_factorization {A : DefSet (M := M) S n m}
    {B : DefSet (M := M) S n l} (T : Chain S n A B) :
    ∃ t : RelativeSpecialChain S n A B, t.toMap = T.toMap := by
  induction T with
  | nil A => exact ⟨.nil A,rfl⟩
  | cons p tail ih =>
    obtain ⟨t,ht⟩ := primitive_relativeSpecial_factorization p
    obtain ⟨u,hu⟩ := ih
    refine ⟨t.append u,?_⟩
    rw [RelativeSpecialChain.append_toMap,ht,hu]
    rfl

theorem special_relativeSpecial_factorization {A : DefSet (M := M) S n m}
    {B : DefSet (M := M) S n l} (T : SpecialBijection A B) :
    ∃ t : RelativeSpecialChain S n A B, t.toMap = T.toMap :=
  chain_relativeSpecial_factorization T.chain

end IntegrationInACVF.Section5
