import IntegrationSection4.PositionRows
import IntegrationSection4.TaggedRVMaps

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5

namespace IntegrationInACVF.Section4

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def PositionRow.transport {G : GammaParameters.Base (M := M)} {m q r : ℕ}
    {A B : Set (Point (M := M) 1 m)} {P : GammaRVMap G A q} {Q : GammaRVMap G B r}
    {a₀ : A} {b₀ : B} {f : (Fin m → M) → M → M} {j : Fin m}
    (row : PositionRow P a₀ f j)
    (hF : {p | ∃ b : B, b.val = p ∧ Q.toFun b = Q.toFun b₀} =
      {p | ∃ a : A, a.val = p ∧ P.toFun a = P.toFun a₀})
    (hLabels : b₀.val.2 = a₀.val.2) : PositionRow Q b₀ f j where
  domain := row.domain
  position := row.position
  fibre := by
    rw [hF,row.fibre,hLabels]
  value := by
    intro x hx
    have hContext : GammaFamilySyntax.labels b₀.val = GammaFamilySyntax.labels a₀.val :=
      congrArg (fun v : Fin m → RV (M := M) => fun i => (v i).val) hLabels
    rw [hContext]
    exact row.value x hx
  cell := by
    intro hPoly
    have hp := congrFun hLabels j
    rw [hp] at hPoly ⊢
    exact row.cell hPoly

namespace GammaRVMap

theorem restrict_same_fibre {G : GammaParameters.Base (M := M)} {n m d : ℕ}
    {A : Set (Point (M := M) n m)} (P : GammaRVMap G A d)
    (D : Set (Point (M := M) n m)) (hDA : D ⊆ A) (hD : GammaSetDefinable G D)
    (hAD : A ⊆ D) (a₀ : D) :
    {p | ∃ a : D, a.val = p ∧ (P.restrict D hDA hD).toFun a = (P.restrict D hDA hD).toFun a₀} =
    {p | ∃ a : A, a.val = p ∧ P.toFun a = P.toFun ⟨a₀.val,hDA a₀.property⟩} := by
  ext p
  exact ⟨fun ⟨a,ha,he⟩ => ⟨⟨a.val,hDA a.property⟩,ha,he⟩,
    fun ⟨a,ha,he⟩ => ⟨⟨a.val,hAD a.property⟩,ha,he⟩⟩

theorem join_reflects_rv {G : GammaParameters.Base (M := M)} {n m d e : ℕ}
    {A D : Set (Point (M := M) n m)} (P : GammaRVMap G A d) (Q : GammaRVMap G D e)
    (hAD : Disjoint A D)
    (hP : ∀ a b, P.toFun a = P.toFun b → SameRV a.val b.val)
    (hQ : ∀ a b, Q.toFun a = Q.toFun b → SameRV a.val b.val)
    (a b : ↥(A ∪ D)) (he : (join P Q hAD).toFun a = (join P Q hAD).toFun b) :
    SameRV a.val b.val := by
  by_cases ha : a.val ∈ A
  · let c : A := ⟨a.val,ha⟩
    have hbase : (join P Q hAD).toFun ⟨c.val,Or.inl c.property⟩ = (join P Q hAD).toFun a :=
      congrArg (join P Q hAD).toFun (Subtype.ext rfl)
    obtain ⟨z,hz,hv⟩ := (Set.ext_iff.mp (join_left_fibre P Q hAD c) b.val).mp
      ⟨b,rfl,he.symm.trans hbase.symm⟩
    exact hz ▸ hP c z hv.symm
  · have haD := a.property.resolve_left ha
    let c : D := ⟨a.val,haD⟩
    have hbase : (join P Q hAD).toFun ⟨c.val,Or.inr c.property⟩ = (join P Q hAD).toFun a :=
      congrArg (join P Q hAD).toFun (Subtype.ext rfl)
    obtain ⟨z,hz,hv⟩ := (Set.ext_iff.mp (join_right_fibre P Q hAD c) b.val).mp
      ⟨b,rfl,he.symm.trans hbase.symm⟩
    exact hz ▸ hQ c z hv.symm

end GammaRVMap
end IntegrationInACVF.Section4
