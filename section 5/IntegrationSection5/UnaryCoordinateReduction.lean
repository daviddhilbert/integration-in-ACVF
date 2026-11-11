import IntegrationSection5.CoordinateIsoPartition
import IntegrationSection5.GammaIsoCoordinates
import IntegrationSection5.CodedCoordinateUpdate
import IntegrationSection5.GammaSwapFactorization

/-! A constructed unary-chain prefix makes one additional target coordinate
fixed. The remaining bijection has a strictly smaller active coordinate set. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n p m w : ℕ}

structure UnaryCoordinateReduction {A : Set (Point (M := M) n m)} {B : Set (Point (M := M) n w)}
    (e : GammaIso G A B) (F : Finset (Fin n)) (D : Set (Point (M := M) n m)) (hDA : D ⊆ A) where
  coordinate : Fin n
  coordinate_mem : coordinate ∈ F
  arity : ℕ
  target : Set (Point (M := M) n arity)
  chain : GammaUnaryChain G n D target
  remainder : GammaIso G target (gammaRestrictionTarget e D hDA)
  commutes : ∀ a : D, (remainder.equiv (chain.toIso.equiv a)).val =
    (e.equiv ⟨a.val,hDA a.property⟩).val
  fixed : ∀ c : target, ∀ k : Fin n, k ∉ F.erase coordinate → (remainder.equiv c).val.1 k = c.val.1 k

theorem coordinate_piece_reduction {A : Set (Point (M := M) (p+1) m)}
    {B : Set (Point (M := M) (p+1) w)} (e : GammaIso G A B) (i : Fin (p+1))
    (P : CoordinateRVPartition G i e.equiv) (F : Finset (Fin (p+1))) (hi : i ∈ F)
    (hfix : ∀ a : A, ∀ j : Fin (p+1), j ∉ F → (e.equiv a).val.1 j = a.val.1 j)
    (k : Option (Fin (p+1))) :
    Nonempty (UnaryCoordinateReduction e F (P.pieces k) (P.subset k)) := by
  let D := P.pieces k
  let hDA := P.subset k
  let er := gammaRestrictionIso e D hDA (P.definable k)
  obtain ⟨j,hj,hinj⟩ := P.active_coordinate F hi hfix k
  let Q := P.code.restrict D hDA (P.definable k)
  let g : D → VF (M := M) := fun a => vfAt (er.equiv a).val j
  have hg := gamma_iso_coordinate_scalar_graph er j
  have hinj' : ∀ a b : D, SameCoordinateContext i a.val b.val →
      Q.toFun a = Q.toFun b → g a = g b → a = b := by
    intro a b hctx hcode hscalar
    have h := hinj ⟨a.val,hDA a.property⟩ ⟨b.val,hDA b.property⟩ a.property b.property hctx hcode hscalar
    exact Subtype.ext (congrArg (fun a : A => a.val) h)
  obtain ⟨C,T,hT⟩ := coded_coordinate_unary_factorization Q i g hg hinj'
  obtain ⟨C',U,hU⟩ := gamma_swap_unary_factorization C (T.toIso.target_definable (gammaLogicInput G)) i j
  let V := T.append U
  let rem := (V.toIso.symm (gammaLogicInput G)).trans (gammaLogicInput G) er
  have hV (a : D) : (V.toIso.equiv a).val =
      vfPermutation (Equiv.swap i j) (codedCoordinateUpdate Q i g a) := by
    exact (congrArg (fun c : C' => c.val) (T.append_apply U a)).trans
      ((hU (T.toIso.equiv a)).trans (congrArg (vfPermutation (Equiv.swap i j)) (hT a)))
  refine ⟨⟨j,hj,m+P.arity,C',V,rem,?_,?_⟩⟩
  · intro a
    change (er.equiv (V.toIso.equiv.symm (V.toIso.equiv a))).val = _
    rw [V.toIso.equiv.symm_apply_apply]
    rfl
  · intro c q hq
    obtain ⟨a,rfl⟩ := V.toIso.equiv.surjective c
    change (er.equiv (V.toIso.equiv.symm (V.toIso.equiv a))).val.1 q = _
    rw [V.toIso.equiv.symm_apply_apply,hV a]
    by_cases hqj : q = j
    · subst q
      simp only [vfPermutation,Function.comp_apply,Equiv.swap_apply_right,
        codedCoordinateUpdate,replace,Function.update_self]
      rfl
    · have hqF : q ∉ F := fun h => hq (Finset.mem_erase.mpr ⟨hqj,h⟩)
      have hqi : q ≠ i := fun h => hqF (h.symm ▸ hi)
      have hfixa : (er.equiv a).val.1 q = a.val.1 q := by
        change (e.equiv ⟨a.val,hDA a.property⟩).val.1 q = a.val.1 q
        exact hfix ⟨a.val,hDA a.property⟩ q hqF
      simpa only [vfPermutation,Function.comp_apply,Equiv.swap_apply_of_ne_of_ne hqi hqj,
        codedCoordinateUpdate,replace,Function.update_of_ne hqi,GammaRVMap.attachment] using hfixa

end IntegrationInACVF.Section5
