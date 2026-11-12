import Section3.GammaFullDescent

/-! Tuple parameter promotion retains the original Gamma names and global
representative invariance. This is the family version of the checked scalar
promotion in `Section3.GammaFullDescent`, using its support-hull construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem gamma_tuple_parameter_promotion (B : Base (M := M)) {n m : ℕ}
    (sa : Fin n → SortTag) (sb : Fin m → SortTag)
    (a : Fin n → M) (ha : ∀ i, sortEval (sa i) (a i))
    (W : Set (Fin m → M)) (hW : DefinableOverBase ⟨B.real ∪ Set.range a,B.gamma⟩ sb W) :
    ∃ P : Set ((Fin n → M) × (Fin m → M)),
      DefinableOverBase B (Fin.append sa sb)
        {z | ((fun i => z (Fin.castAdd m i)),fun j => z (Fin.natAdd n j)) ∈ P} ∧
      {x | (a,x) ∈ P} = W := by
  obtain ⟨k,γ,hγ,Q,hQW⟩ := hW
  obtain ⟨H,hHd,hHi,hHa⟩ := promote_gamma_relation B.real a Q
  let sm := Fin.append sa sb
  have hSort (i : Fin (n+m)) :=
    ((definableAt_iff_normalized_raw B.real (sm i) {x | sortEval (sm i) x}).mp
      (definableAt_sort B.real (sm i))).1
  have hProper := proper_normalized_definable (M := M) B.real (n := k)
  let R : Relation B.real k (n+m) sm :=
    { carrier := {p | Proper p.1 ∧ (∀ i, sortEval (sm i) (p.2 i)) ∧
        ((fun i => p.2 (Fin.castAdd m i)),p.1,fun j => p.2 (Fin.natAdd n j)) ∈ H}
      definable := by
        let N := CanonicalStructure.normalize (M := M)
        letI := N
        let idx : Fin n ⊕ (Fin k ⊕ Fin m) → Fin k ⊕ Fin (n+m) :=
          Sum.elim (fun i => .inr (Fin.castAdd m i))
            (Sum.elim Sum.inl (fun j => .inr (Fin.natAdd n j)))
        have hh := hHd.preimage_comp idx
        have hp := hProper.preimage_comp (Sum.inl : Fin k → Fin k ⊕ Fin (n+m))
        have hs := Set.definable_iInter_of_finite (fun i =>
          (hSort i).preimage_comp (fun _ : Fin 1 => (Sum.inr i : Fin k ⊕ Fin (n+m))))
        convert hp.inter (hs.inter hh) using 1
        ext z
        simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter,Set.mem_preimage,
          Function.comp_apply]
        rfl
      proper := fun p hp => ⟨hp.1,hp.2.1⟩
      invariant := by
        intro t u htu z
        change (Proper (rawTuple t) ∧ (∀ i, sortEval (sm i) (z i)) ∧ _) ↔
          (Proper (rawTuple u) ∧ (∀ i, sortEval (sm i) (z i)) ∧ _)
        simp only [rawTuple_proper,true_and]
        exact and_congr Iff.rfl (hHi _ _ t u htu) }
  let c := rawTuple (representatives γ)
  have hrow : {x | (c,Fin.append a x) ∈ R.carrier} = W := by
    ext x
    have hQx : (c,x) ∈ Q.carrier ↔ x ∈ W := Set.ext_iff.mp hQW x
    have hh := hHa c x (rawTuple_proper (representatives γ))
    constructor
    · intro hx
      exact hQx.mp (hh.mp (by simpa only [Fin.append_left,Fin.append_right] using hx.2.2))
    · intro hx
      have hqx := hQx.mpr hx
      refine ⟨rawTuple_proper (representatives γ),?_,?_⟩
      · intro i
        refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa only [sm,Fin.append_left] using ha j
        · simpa only [sm,Fin.append_right] using (Q.proper _ hqx).2 j
      · simpa only [Fin.append_left,Fin.append_right] using hh.mpr hqx
  let P : Set ((Fin n → M) × (Fin m → M)) := {p | (c,Fin.append p.1 p.2) ∈ R.carrier}
  refine ⟨P,⟨k,γ,hγ,R,?_⟩,hrow⟩
  ext z
  change (c,z) ∈ R.carrier ↔
    (c,Fin.append (fun i => z (Fin.castAdd m i)) (fun j => z (Fin.natAdd n j))) ∈ R.carrier
  rw [Fin.append_castAdd_natAdd]

end IntegrationInACVF.Section6
