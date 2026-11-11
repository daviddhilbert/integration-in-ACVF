import IntegrationSection5.AllConstantAttachment

/-! A finite original-Gamma partition choosing the first nonconstant scalar
branch, with a separate all-constant piece. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {p m u d : ℕ}
variable {D : Set (Point (M := M) (p+1) m)}

def scalarPrefixIndices (j : Fin u → Fin d) (i : Fin u) : Fin i.val → Fin d :=
  fun k => j ⟨k.val,lt_trans k.isLt i.isLt⟩

def scalarTagPiece (Q : GammaRVMap G D d) (j : Fin u → Fin d) :
    Option (Fin u) → Set (Point (M := M) (p+1) m)
  | none => allConstantDomain Q j
  | some i => allConstantDomain Q (scalarPrefixIndices j i) \
      allConstantDomain Q (fun _ : Fin 1 => j i)

theorem scalarTagPiece_definable (Q : GammaRVMap G D d) (j : Fin u → Fin d)
    (i : Option (Fin u)) : GammaSetDefinable G (scalarTagPiece Q j i) := by
  cases i with
  | none => exact allConstantDomain_definable Q j
  | some i =>
    exact (gammaLogicInput G).sdiff (allConstantDomain_definable Q _)
      (allConstantDomain_definable Q _)

theorem scalarTagPiece_subset (Q : GammaRVMap G D d) (j : Fin u → Fin d)
    (i : Option (Fin u)) : scalarTagPiece Q j i ⊆ D := by
  cases i with
  | none => exact allConstantDomain_subset Q j
  | some i => exact fun _ h => allConstantDomain_subset Q _ h.1

theorem mem_scalarTagPiece_some (Q : GammaRVMap G D d) (j : Fin u → Fin d)
    (i : Fin u) (a : D) : a.val ∈ scalarTagPiece Q j (some i) ↔
      (∀ k : Fin u, k < i → Q.toFun a (j k) = rv (0 : VF (M := M))) ∧
      Q.toFun a (j i) ≠ rv (0 : VF (M := M)) := by
  change (a.val ∈ allConstantDomain Q (scalarPrefixIndices j i) ∧
    a.val ∉ allConstantDomain Q (fun _ : Fin 1 => j i)) ↔ _
  rw [mem_allConstantDomain,mem_allConstantDomain]
  constructor
  · rintro ⟨hp,hi⟩
    refine ⟨fun k hk => hp ⟨k.val,hk⟩,?_⟩
    exact fun h => hi (fun _ => h)
  · rintro ⟨hp,hi⟩
    exact ⟨fun k => hp ⟨k.val,lt_trans k.isLt i.isLt⟩ k.isLt,fun h => hi (h 0)⟩

theorem scalarTagPiece_cover (Q : GammaRVMap G D d) (j : Fin u → Fin d)
    (a : D) : ∃ i : Option (Fin u), a.val ∈ scalarTagPiece Q j i := by
  let F : Finset (Fin u) := Finset.univ.filter (fun i => Q.toFun a (j i) ≠ rv (0 : VF (M := M)))
  by_cases hF : F.Nonempty
  · let i := F.min' hF
    have hi : Q.toFun a (j i) ≠ rv (0 : VF (M := M)) := (Finset.mem_filter.mp (Finset.min'_mem F hF)).2
    refine ⟨some i,(mem_scalarTagPiece_some Q j i a).mpr ⟨?_,hi⟩⟩
    intro k hk
    by_contra hn
    have hkF : k ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩
    exact (not_le_of_gt hk) (Finset.min'_le F k hkF)
  · refine ⟨none,(mem_allConstantDomain Q j a).mpr ?_⟩
    intro i
    by_contra hn
    exact hF ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩⟩

theorem scalarTagPiece_disjoint (Q : GammaRVMap G D d) (j : Fin u → Fin d)
    {i k : Option (Fin u)} (hik : i ≠ k) : Disjoint (scalarTagPiece Q j i) (scalarTagPiece Q j k) := by
  apply Set.disjoint_left.mpr
  intro a hai hak
  let b : D := ⟨a,scalarTagPiece_subset Q j i hai⟩
  cases i with
  | none =>
    cases k with
    | none => exact hik rfl
    | some k =>
      have hz := (mem_allConstantDomain Q j b).mp hai
      exact ((mem_scalarTagPiece_some Q j k b).mp hak).2 (hz k)
  | some i =>
    have hi := (mem_scalarTagPiece_some Q j i b).mp hai
    cases k with
    | none => exact hi.2 ((mem_allConstantDomain Q j b).mp hak i)
    | some k =>
      have hk := (mem_scalarTagPiece_some Q j k b).mp hak
      rcases lt_trichotomy i k with hlt | heq | hgt
      · exact hi.2 (hk.1 i hlt)
      · exact hik (congrArg some heq)
      · exact hk.2 (hi.1 k hgt)

end IntegrationInACVF.Section5
