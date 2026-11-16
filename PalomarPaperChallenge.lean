module
public import Mathlib
meta import all Lean.Meta.Match.Match
meta import Lean.Meta.Tactic.AuxLemma
@[expose] public section
/-! # Geometric preparation for integration in ACVF
This independent Challenge selects two results of Yimu Yin's
Integration in algebraically closed valued fields, arXiv:0809.0473v2.
Proposition 3.19 partitions an actual original-base definable VF bijection
into finitely many nonempty, disjoint, definable open-to-open pieces.
Lemma 4.8 decomposes an original-Gamma-base definable subset of VF² into
the two-cell fibres of a definable map to a finite RV power. The cell
positioning graph and both paradigms are definable over the original base
with the output RV tuple. The displayed model, characteristic, saturation,
parameter-base and named-value hypotheses remain part of the claims.
Definitions below retain their ordinary mathematical meaning and actual
computational data. Only theorem proofs are left unspecified; the Solution
imports the proved implementation and does not import this Challenge.
Other Sections 2–7 results in the repository are outside this selection.
-/
/- Clearing two compiler caches preserves the copied source-module
boundaries and generated names; it does not change mathematical declarations. -/
open Lean Elab Command in
elab "reset_statement_module_caches" : command => do
  let cache : Name := `_private.Lean.Meta.Match.Match ++ .num .anonymous 0 ++ `Lean.Meta.Match.matcherExt
  unless (← getEnv).contains cache do throwError "Pinned Lean matcher cache is unavailable"
  elabCommand (← `(command| run_cmd do
    Lean.modifyEnv (fun env => Lean.EnvExtension.modifyState $(mkIdent cache)
      (Lean.Meta.auxLemmasExt.modifyState env (fun _ => {})) (fun _ => {}))))
set_option maxHeartbeats 4000000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency false
namespace IntegrationInACVF.Section3ACVF.BallCosetAtomicity
end IntegrationInACVF.Section3ACVF.BallCosetAtomicity
namespace IntegrationInACVF.Section3ACVF.CanonicalBallSupport
end IntegrationInACVF.Section3ACVF.CanonicalBallSupport
namespace IntegrationInACVF.Section3ACVF.GammaTailMap
end IntegrationInACVF.Section3ACVF.GammaTailMap
namespace IntegrationInACVF.Section3ACVF.NamedRadiusAtomicity
end IntegrationInACVF.Section3ACVF.NamedRadiusAtomicity
namespace IntegrationInACVF.Section3ACVF.PuncturedGeometry
end IntegrationInACVF.Section3ACVF.PuncturedGeometry
namespace IntegrationInACVF.Section3ACVF.ThinFamilyGeometry
end IntegrationInACVF.Section3ACVF.ThinFamilyGeometry
namespace SpecialTransformations.Section4
end SpecialTransformations.Section4
reset_statement_module_caches section @[expose] public section open FirstOrder FirstOrder.Language namespace SpecialTransformations namespace Milestone0 namespace Valued open Valuation end Valued
/-- The sorts of `L_RV`, as tags on the single carrier. -/ inductive SortTag where
  | vf
  | rv
  deriving DecidableEq, Repr
/-- Function symbols of `L_RV`, tagged by arity. -/ inductive Fn : ℕ → Type where/-- `0` of the ring language of the `VF` sort -/ | vfZero : Fn 0/-- `1` of the ring language of the `VF` sort -/ | vfOne : Fn 0/-- `+` of the ring language of the `VF` sort -/ | vfAdd : Fn 2/-- `-` of the ring language of the `VF` sort -/ | vfNeg : Fn 1/-- `×` of the ring language of the `VF` sort -/ | vfMul : Fn 2/-- `1` of the group language of the `RV` sort -/ | rvOne : Fn 0/-- the constant `0` of the `RV` sort: the residue field's zero, which is also `rv(0)` and the absorbing element of `RV`. The paper writes this element both as `0` and as `∞`; it is one element, so the language has one constant. -/ | rvZero : Fn 0/-- `×` of the `RV` sort -/ | rvMul : Fn 2/-- Multiplicative inverse on `RV`, totalized by `0⁻¹ = 0`. Naming this symbol is the author-approved correction to the inverse-free language specification before Convention 2.5, required for the intended QE result. It ensures that language substructures contain RV inverses. See LANGUAGE-ERRATA.md. -/ | rvInv : Fn 1/-- `+ : K² → K` of the `RV` sort -/ | kAdd : Fn 2/-- `- : K → K` of the `RV` sort -/ | kNeg : Fn 1/-- the projection `rv : VF → RV` -/ | rvMap : Fn 1
/-- Relation symbols of `L_RV`, tagged by arity. The first two are the sort predicates of the encoding (they are not part of the paper's signature); the last two are the paper's unary predicate `Kˣ` and its preorder `≤`. -/ inductive Rel : ℕ → Type where/-- encoding: the `VF` sort -/ | memVF : Rel 1/-- encoding: the `RV` sort -/ | memRV : Rel 1/-- the paper's unary predicate `Kˣ` -/ | memUnits : Rel 1/-- the paper's preorder `≤` on `RV` -/ | rvLe : Rel 2
/-- The corrected `L_RV`, with named RV inversion, in the tagged one-sorted encoding. -/ def LRV : Language :=
  ⟨Fn, Rel⟩
namespace LRV
/-- Terms of `L_RV` whose (free) variables are indexed by `Fin n`. -/ abbrev Tm (n : ℕ) : Type :=
  LRV.Term (Empty ⊕ Fin n)
/-- Bounded formulas of `L_RV` with `n` variables in scope and no free parameters. -/ abbrev Bf (n : ℕ) : Type :=
  LRV.BoundedFormula Empty n
variable {n : ℕ}
/-- `0` of the `VF` sort -/ def tVFZero : Tm n :=
  Term.func Fn.vfZero fun i => i.elim0
/-- `1` of the `VF` sort -/ def tVFOne : Tm n :=
  Term.func Fn.vfOne fun i => i.elim0
/-- `+` of the `VF` sort -/ def tVFAdd (t u : Tm n) : Tm n :=
  Term.func Fn.vfAdd ![t, u]
/-- `-` of the `VF` sort -/ def tVFNeg (t : Tm n) : Tm n :=
  Term.func Fn.vfNeg ![t]
/-- `×` of the `VF` sort -/ def tVFMul (t u : Tm n) : Tm n :=
  Term.func Fn.vfMul ![t, u]
/-- `1` of the `RV` sort -/ def tRVOne : Tm n :=
  Term.func Fn.rvOne fun i => i.elim0
/-- `0` of the `RV` sort -/ def tRVZero : Tm n :=
  Term.func Fn.rvZero fun i => i.elim0
/-- The paper's `∞` is `rv(0)`, i.e. the absorbing element `rvZero` of the `RV` sort: the paper's two symbols `0` and `∞` name one element. Kept as a definition so that the axioms can be read in the paper's notation. -/ def tRVInfty : Tm n :=
  tRVZero
/-- `×` of the `RV` sort -/ def tRVMul (t u : Tm n) : Tm n :=
  Term.func Fn.rvMul ![t, u]
/-- Multiplicative inverse on the `RV` sort, with `0⁻¹ = 0`. -/ def tRVInv (t : Tm n) : Tm n :=
  Term.func Fn.rvInv ![t]
/-- `+ : K² → K` of the `RV` sort -/ def tKAdd (t u : Tm n) : Tm n :=
  Term.func Fn.kAdd ![t, u]
/-- `- : K → K` of the `RV` sort -/ def tKNeg (t : Tm n) : Tm n :=
  Term.func Fn.kNeg ![t]
/-- the projection `rv : VF → RV` -/ def tRv (t : Tm n) : Tm n :=
  Term.func Fn.rvMap ![t]
/-- the bound variable of index `i < n` -/ def tv (i : ℕ) (h : i < n) : Tm n :=
  Term.var (Sum.inr ⟨i, h⟩)
/-- the numeral `k · 1` of the `VF` sort -/ def tVFNumeral : ℕ → Tm n
  | 0 => tVFZero
  | k + 1 => tVFAdd (tVFNumeral k) tVFOne
/-- `t ^ k`, in the `RV` sort -/ def tRVPow (t : Tm n) : ℕ → Tm n
  | 0 => tRVOne
  | k + 1 => tRVMul (tRVPow t k) t
/-- `t ∈ VF`, the encoding's sort predicate for the `VF` sort -/ def pVF (t : Tm n) : Bf n :=
  FirstOrder.Language.Relations.boundedFormula₁ Rel.memVF t
/-- `t ∈ RV`, the encoding's sort predicate for the `RV` sort -/ def pRVsort (t : Tm n) : Bf n :=
  FirstOrder.Language.Relations.boundedFormula₁ Rel.memRV t
/-- the paper's unary predicate `Kˣ` -/ def pUnits (t : Tm n) : Bf n :=
  FirstOrder.Language.Relations.boundedFormula₁ Rel.memUnits t
/-- the paper's preorder `≤` -/ def pLe (t u : Tm n) : Bf n :=
  FirstOrder.Language.Relations.boundedFormula₂ Rel.rvLe t u
/-- `t = u` -/ def pEq (t u : Tm n) : Bf n :=
  t =' u
/-- the paper's `RV = RV-sort ∖ {0}` -/ def pRV (t : Tm n) : Bf n :=
  ∼(pEq t tRVZero)
/-- the strict order `t > 1` of the `RV` sort -/ def pGtOne (t : Tm n) : Bf n :=
  pLe tRVOne t ⊓ ∼(pLe t tRVOne)
/-- `t ∈ K = K^× ∪ {0}`, the residue field inside the `RV` sort. Not the same as `t ≠ 0`: when `Γ` is nontrivial the elements of `RV ∖ {0}` of value `≠ 1` are not in `K`, and the residue-field operations are junk there. Definition 2.1(d) defines `K` as `K^× ∪ {0}`, with `K^×` the predicate, i.e. axiom (4)'s class of `1`. The `0` here is `rv(0)`, the absorbing element of `RV`. -/ def pInK (t : Tm n) : Bf n :=
  pUnits t ⊔ pEq t tRVZero
end LRV namespace LRV
/-- the sort predicate of the sort `s`, as a formula -/ def sortPred (s : SortTag) (t : Tm n) : Bf n :=
  match s with
  | .vf => pVF t
  | .rv => pRVsort t
/-- `⋀ i, x_i ∈ s_i`, for the variables `x_i` of index `i` -/ def sortedHyps {k : ℕ} (ss : Fin k → SortTag) : Bf k :=
  (List.finRange k).foldr (fun i acc => sortPred (ss i) (tv i.val i.isLt) ⊓ acc) ⊤
/-- the guarded universal sentence `∀ x̄, (⋀ i, x_i ∈ s_i) → φ` -/ def allSorted {k : ℕ} (ss : Fin k → SortTag) (φ : Bf k) : LRV.Sentence :=
  BoundedFormula.alls (sortedHyps ss ⟹ φ)
/-- the guarded existential formula `∃ x ∈ s, φ`, where `x` is the variable of index `k` -/ def exSorted {k : ℕ} (s : SortTag) (φ : Bf (k + 1)) : Bf k :=
  BoundedFormula.ex (sortPred s (tv k (Nat.lt_succ_self k)) ⊓ φ)
/-- `⋀ i < k, x_i ∈ K`: the tuple lies in `K = K^× ∪ {0}` -/ def kHyps {k : ℕ} : Bf k :=
  (List.finRange k).foldr (fun i acc => pInK (tv i.val i.isLt) ⊓ acc) ⊤
/-- the universal sentence `∀ x̄ ∈ s̄ ∩ K, φ` -/ def allSortedK {k : ℕ} (ss : Fin k → SortTag) (φ : Bf k) : LRV.Sentence :=
  BoundedFormula.alls ((sortedHyps ss ⊓ kHyps) ⟹ φ)
/-- the guarded existential formula `∃ x ∈ s ∩ K, φ`, with `x` the variable of index `k` -/ def exSortedK {k : ℕ} (s : SortTag) (φ : Bf (k + 1)) : Bf k :=
  BoundedFormula.ex (sortPred s (tv k (Nat.lt_succ_self k)) ⊓ pInK (tv k (Nat.lt_succ_self k)) ⊓ φ)
/-- the universal closure of a formula in a single variable -/ def allOne (φ : Bf 1) : LRV.Sentence :=
  BoundedFormula.alls φ
/-- The result sort of a function symbol of `L_RV`. -/ def Fn.resSort : {l : ℕ} → Fn l → SortTag
  | _, .vfZero => .vf
  | _, .vfOne => .vf
  | _, .vfAdd => .vf
  | _, .vfNeg => .vf
  | _, .vfMul => .vf
  | _, .rvOne => .rv
  | _, .rvZero => .rv
  | _, .rvMul => .rv
  | _, .rvInv => .rv
  | _, .kAdd => .rv
  | _, .kNeg => .rv
  | _, .rvMap => .rv
/-- The sort of the `i`-th argument of a function symbol of `L_RV`. -/ def Fn.argSort : {l : ℕ} → (f : Fn l) → Fin l → SortTag
  | _, .vfZero => Fin.elim0
  | _, .vfOne => Fin.elim0
  | _, .vfAdd => fun _ => .vf
  | _, .vfNeg => fun _ => .vf
  | _, .vfMul => fun _ => .vf
  | _, .rvOne => Fin.elim0
  | _, .rvZero => Fin.elim0
  | _, .rvMul => fun _ => .rv
  | _, .rvInv => fun _ => .rv
  | _, .kAdd => fun _ => .rv
  | _, .kNeg => fun _ => .rv
  | _, .rvMap => fun _ => .vf
section TmSortLemmas variable {α : Type} (sα : α → SortTag) {n : ℕ} (sn : Fin n → SortTag) end TmSortLemmas section FormulaLemmas variable {α : Type} (sα : α → SortTag) {n : ℕ} (sn : Fin n → SortTag) end FormulaLemmas section SortedHyps variable (sα : Empty → SortTag) end SortedHyps section OccursHyps end OccursHyps section Alls end Alls section Connectives variable {α : Type} (sα : α → SortTag) {n : ℕ} (sn : Fin n → SortTag) end Connectives section Variables variable (sα : Empty → SortTag) {n : ℕ} (sn : Fin n → SortTag) end Variables section Existentials variable (sα : Empty → SortTag) end Existentials section SortedHypsGeneric variable (sα : Empty → SortTag) end SortedHypsGeneric section TmSortConstructors variable (sα : Empty → SortTag) {n : ℕ} (sn : Fin n → SortTag) end TmSortConstructors section Powers variable (sα : Empty → SortTag) {n : ℕ} (sn : Fin n → SortTag) end Powers
/-- Horner form `x^k + a_{k-1} x^{k-1} + ⋯ + a_0` of the monic polynomial of degree `k` whose coefficients are the variables `0, …, k-1` and whose variable is the variable `k`. The leading term is `x ^ k`, so `acfScheme` quantifies over *all* monic polynomials of degree `k`. (An earlier version started the Horner fold at `x` instead of at `x + a_{k-1}`, which silently produced `x^{k+1} + a_{k-1}x^{k-1} + ⋯ + a_0` — a monic polynomial of degree `k+1` with zero `x^k` coefficient, so the scheme covered only a proper subclass and did not give algebraic closedness.) For `k = 0` the value is immaterial: `acfScheme` is only used with `1 ≤ k`. -/ def hornerPoly {k : ℕ} (add mul : {n : ℕ} → Tm n → Tm n → Tm n) : Tm (k + 1) :=
  match k with
  | 0 => tv 0 Nat.zero_lt_one
  | (n + 1) =>
    let x : Tm (n + 1 + 1) := tv (n + 1) (Nat.lt_succ_self (n + 1))
    (List.finRange n).reverse.foldl (fun acc i => add (mul acc x) (tv i.val (Nat.lt_trans i.isLt (Nat.lt.step (Nat.lt_succ_self n))))) (add x (tv n (Nat.lt.step (Nat.lt_succ_self n))))
end LRV namespace Axioms open LRV
/-- The sentences of a finite list, as a theory. -/ def ofList (l : List LRV.Sentence) : LRV.Theory :=
  {s | s ∈ l}
/-- the carrier is covered by the two sorts -/ def sdCover : LRV.Sentence :=
  allOne (pVF &0 ⊔ pRVsort &0)
/-- the two sorts are disjoint -/ def sdDisjoint : LRV.Sentence :=
  allOne (∼(pVF &0 ⊓ pRVsort &0))
/-- `0` of the ring language lies in the `VF` sort -/ def sdVFZero : LRV.Sentence :=
  pVF tVFZero
/-- `1` of the ring language lies in the `VF` sort -/ def sdVFOne : LRV.Sentence :=
  pVF tVFOne
/-- the `VF` sort is closed under `+` -/ def sdVFAdd : LRV.Sentence :=
  allSorted ![.vf, .vf] (pVF (tVFAdd (&0) &1))
/-- the `VF` sort is closed under `-` -/ def sdVFNeg : LRV.Sentence :=
  allSorted ![.vf] (pVF (tVFNeg &0))
/-- the `VF` sort is closed under `×` -/ def sdVFMul : LRV.Sentence :=
  allSorted ![.vf, .vf] (pVF (tVFMul (&0) &1))
/-- `rv` maps the `VF` sort into the `RV` sort -/ def sdRv : LRV.Sentence :=
  allSorted ![.vf] (pRVsort (tRv &0))
/-- `0` of the `RV` sort lies in the `RV` sort -/ def sdRVZero : LRV.Sentence :=
  pRVsort tRVZero
/-- `∞` lies in the `RV` sort -/ def sdRVInfty : LRV.Sentence :=
  pRVsort tRVInfty
/-- `1` of the `RV` sort lies in the `RV` sort -/ def sdRVOne : LRV.Sentence :=
  pRVsort tRVOne
/-- the `RV` sort is closed under `×` -/ def sdRVMul : LRV.Sentence :=
  allSorted ![.rv, .rv] (pRVsort (tRVMul (&0) &1))
def sdRVInv : LRV.Sentence :=
  allSorted ![.rv] (pRVsort (tRVInv &0))
/-- The predicate `Kˣ` holds only of elements of the `RV` sort. Its actual content is axiom (4)'s `leClassOne`, which makes `Kˣ` the class of `1` — a *proper* subgroup of the multiplicative group `RV ∖ {0}` whenever `Γ` is nontrivial. Identifying `Kˣ` with all of `RV ∖ {0}` puts every `x ≠ 0` in the class of `1`, hence `1 ≤ x ≤ 1`, hence makes the preorder trivial and `Γ` trivial — contradicting the paper's standing hypothesis that `Γ(S)` is nontrivial. -/ def sdUnits : LRV.Sentence :=
  allOne (pUnits &0 ⟹ pRVsort &0)
/-- `K = Kˣ ∪ {0}` is closed under `+` -/ def sdKAdd : LRV.Sentence :=
  allSorted ![.rv, .rv] (pInK &0 ⟹ (pInK &1 ⟹ pInK (tKAdd (&0) &1)))
/-- `K` is closed under unary `-` -/ def sdKNeg : LRV.Sentence :=
  allSorted ![.rv] (pInK &0 ⟹ pInK (tKNeg &0))
/-- `K` is closed under `×`: the paper's `K = K^× ∪ {0}` is a field, so the product of two elements of `K` is in `K` and not `∞`. Without this the field axioms of `kField` (which are guarded by `pK`) constrain only the products that happen to land in `K`. -/ def sdKMul : LRV.Sentence :=
  allSorted ![.rv, .rv] (pInK &0 ⟹ (pInK &1 ⟹ pInK (tRVMul (&0) &1)))
/-- The closure part of the sort discipline: each sort is closed under its own symbols, and the two sorts are related through the symbols that cross them. -/ def sortClosure : LRV.Theory :=
  ofList [sdVFZero, sdVFOne, sdVFAdd, sdVFNeg, sdVFMul, sdRv, sdRVZero, sdRVInfty, sdRVOne, sdRVMul, sdRVInv, sdUnits, sdKAdd, sdKNeg, sdKMul]
/-- the sort discipline of the encoding, as a theory -/ def sortAxioms : LRV.Theory :=
  sortClosure ∪ ofList [sdCover, sdDisjoint]
/-- the field axioms for the sort `s`, with that sort's `0`, `1`, `+`, `-`, `×` -/ def fieldAxioms (s : SortTag) (zero one : {n : ℕ} → Tm n) (add mul : {n : ℕ} → Tm n → Tm n → Tm n) (neg : {n : ℕ} → Tm n → Tm n) : List LRV.Sentence :=
  [ /- associativity of `+` -/
    allSorted ![s, s, s] (pEq (add (add (&0) &1) &2) (add (&0) (add (&1) &2))),
    /- commutativity of `+` -/
    allSorted ![s, s] (pEq (add (&0) &1) (add (&1) &0)),
    /- `0` is neutral for `+` -/
    allSorted ![s] (pEq (add (&0) zero) &0),
    /- additive inverses -/
    allSorted ![s] (pEq (add (&0) (neg &0)) zero),
    /- associativity of `×` -/
    allSorted ![s, s, s] (pEq (mul (mul (&0) &1) &2) (mul (&0) (mul (&1) &2))),
    /- commutativity of `×` -/
    allSorted ![s, s] (pEq (mul (&0) &1) (mul (&1) &0)),
    /- `1` is neutral for `×` -/
    allSorted ![s] (pEq (mul (&0) one) &0),
    /- distributivity -/
    allSorted ![s, s, s] (pEq (mul (&0) (add (&1) &2)) (add (mul (&0) &1) (mul (&0) &2))),
    /- `0 ≠ 1` -/
    ∼(pEq zero one),
    /- every nonzero element is invertible: the language has no inverse symbol -/
    allSorted ![s] (pEq (&0) zero ⊔ exSorted s (pEq (mul (&0) &1) one))]
/-- the algebraic-closedness scheme for the sort `s`: `∀ a₀ … a_{k-1} ∃ x, x^k + a_{k-1} x^{k-1} + ⋯ + a₀ = 0` -/ def acfScheme (s : SortTag) (zero : {n : ℕ} → Tm n) (add mul : {n : ℕ} → Tm n → Tm n → Tm n) (k : ℕ) : LRV.Sentence :=
  allSorted (fun _ : Fin k => s) (exSorted s (pEq (hornerPoly add mul) zero))
/-- Definition 2.2 item 1: `(VF, 0, 1, +, -, ×)` is an algebraically closed field. -/ def vfField : LRV.Theory :=
  ofList (fieldAxioms .vf tVFZero tVFOne tVFAdd tVFMul tVFNeg)
/-- algebraic closedness of the `VF` sort -/ def vfAlgClosed : LRV.Theory :=
  {s | ∃ k, 1 ≤ k ∧ s = acfScheme .vf tVFZero tVFAdd tVFMul k}
/-- Definition 2.2 item 3: `(K, 0, 1, +, -, ×)` is an algebraically closed field, where `K = K^× ∪ {0}`, the units of `RV` together with the absorbing element `0 = ∞ = rv 0`. Every quantifier is relativised to `K` (`allSortedK`, `exSortedK`), not merely to the `RV` sort. This is not cosmetic: `RV^×` also contains the elements of value `≠ 1`, where the residue operations are junk, so asserting the field axioms at every element of `RV` (equivalently at every `t ≠ ∞`, since `RV ∖ {0}` *is* the group) would force `Γ` trivial. -/ def kField : LRV.Theory :=
  ofList
    [ /- associativity of `+` -/
      allSortedK ![.rv, .rv, .rv] (pEq (tKAdd (tKAdd (&0) &1) &2) (tKAdd (&0) (tKAdd (&1) &2))),
      /- commutativity of `+` -/
      allSortedK ![.rv, .rv] (pEq (tKAdd (&0) &1) (tKAdd (&1) &0)),
      /- `0` is neutral for `+` -/
      allSortedK ![.rv] (pEq (tKAdd (&0) tRVZero) &0),
      /- additive inverses -/
      allSortedK ![.rv] (pEq (tKAdd (&0) (tKNeg &0)) tRVZero),
      /- associativity of `×` -/
      allSortedK ![.rv, .rv, .rv] (pEq (tRVMul (tRVMul (&0) &1) &2) (tRVMul (&0) (tRVMul (&1) &2))),
      /- commutativity of `×` -/
      allSortedK ![.rv, .rv] (pEq (tRVMul (&0) &1) (tRVMul (&1) &0)),
      /- `1` is neutral for `×` -/
      allSortedK ![.rv] (pEq (tRVMul (&0) tRVOne) &0),
      /- distributivity -/
      allSortedK ![.rv, .rv, .rv] (pEq (tRVMul (&0) (tKAdd (&1) &2)) (tKAdd (tRVMul (&0) &1) (tRVMul (&0) &2))),
      /- `0 ≠ 1` -/
      ∼(pEq tRVZero tRVOne),
      /- every nonzero element of `K` is invertible -/
      allSortedK ![.rv] (pEq (&0) tRVZero ⊔ exSortedK .rv (pEq (tRVMul (&0) &1) tRVOne))]
/-- the algebraic-closedness scheme for `K = K^× ∪ {0}`: coefficients and root in `K` -/ def acfSchemeK (k : ℕ) : LRV.Sentence :=
  allSortedK (fun _ : Fin k => .rv) (exSortedK .rv (pEq (hornerPoly tKAdd tRVMul) tRVZero))
/-- algebraic closedness of `K = K^× ∪ {0}` -/ def kAlgClosed : LRV.Theory :=
  {s | ∃ k, 1 ≤ k ∧ s = acfSchemeK k}
/-- `1 ∈ Kˣ` -/ def rvOneMem : LRV.Sentence :=
  pUnits tRVOne
/-- `Kˣ` is closed under `×` -/ def rvMulMem : LRV.Sentence :=
  allSorted ![.rv, .rv] (pUnits &0 ⟹ (pUnits &1 ⟹ pUnits (tRVMul (&0) &1)))
/-- `×` is associative on `RV` -/ def rvMulAssoc : LRV.Sentence :=
  allSorted ![.rv, .rv, .rv] (pEq (tRVMul (tRVMul (&0) &1) &2) (tRVMul (&0) (tRVMul (&1) &2)))
/-- `×` is commutative on `RV` -/ def rvMulComm : LRV.Sentence :=
  allSorted ![.rv, .rv] (pEq (tRVMul (&0) &1) (tRVMul (&1) &0))
/-- `1` is neutral for `×` on `Kˣ` -/ def rvMulOne : LRV.Sentence :=
  allSorted ![.rv] (pUnits &0 ⟹ pEq (tRVMul tRVOne &0) &0)
/-- every element of `Kˣ` is invertible in `Kˣ` -/ def rvMulInv : LRV.Sentence :=
  allSorted ![.rv] (pUnits &0 ⟹ exSorted .rv (pUnits &1 ⊓ pEq (tRVMul (&1) &0) tRVOne))
/-- divisibility of `Kˣ`: for every `k ≥ 1`, `∀ x ∈ Kˣ ∃ y ∈ Kˣ, y^k = x` -/ def rvDivisible (k : ℕ) : LRV.Sentence :=
  allSorted ![.rv] (pUnits &0 ⟹ exSorted .rv (pUnits &1 ⊓ pEq (tRVPow (&1) k) &0))
/-- `t × 0 = 0` for `t ∈ K` -/ def rvMulZeroK : LRV.Sentence :=
  allSorted ![.rv] (pInK &0 ⟹ pEq (tRVMul (&0) tRVZero) tRVZero)
/-- `t × 0 = 0` for every `t` of the `RV` sort: the absorbing element. (This is the paper's `t × ∞ = ∞`; `∞ = rv 0 = 0`.) -/ def rvMulInfty : LRV.Sentence :=
  allSorted ![.rv] (pEq (tRVMul (&0) tRVInfty) tRVInfty)
/-- Definition 2.2 item 2: `(RV^×, 1, ×)` is a divisible abelian group, with `×` augmented by `t × 0 = 0`, i.e. `0 = ∞ = rv 0` absorbing. -/ def rvGroup : LRV.Theory :=
  ofList [rvOneMem, rvMulMem, rvMulAssoc, rvMulComm, rvMulOne, rvMulInv, rvMulZeroK, rvMulInfty] ∪ {s | ∃ k, 1 ≤ k ∧ s = rvDivisible k}
/-- `≤` is reflexive on `RV` -/ def leRefl : LRV.Sentence :=
  allSorted ![.rv] (pRV &0 ⟹ pLe (&0) &0)
/-- `≤` is transitive on `RV` -/ def leTrans : LRV.Sentence :=
  allSorted ![.rv, .rv, .rv] (pRV &0 ⟹ (pRV &1 ⟹ (pRV &2 ⟹ (pLe (&0) &1 ⟹ (pLe (&1) &2 ⟹ pLe (&0) &2)))))
/-- `≤` is total on `RV` -/ def leTotal : LRV.Sentence :=
  allSorted ![.rv, .rv] (pRV &0 ⟹ (pRV &1 ⟹ (pLe (&0) &1 ⊔ pLe (&1) &0)))
/-- `∞` is the top element of `RV` -/ def leTop : LRV.Sentence :=
  allSorted ![.rv] (pRV &0 ⟹ pLe (&0) tRVInfty)
/-- `∞ ≤ x` forces `x = ∞`, i.e. `∞` is alone in its class -/ def leInftyEq : LRV.Sentence :=
  allSorted ![.rv] (pRV &0 ⟹ (pLe tRVInfty &0 ⟹ pEq (&0) tRVInfty))
/-- `Kˣ` is the equivalence class of `1` -/ def leClassOne : LRV.Sentence :=
  allSorted ![.rv] (pRV &0 ⟹ (pUnits &0 ⇔ (pLe tRVOne &0 ⊓ pLe (&0) tRVOne)))
/-- `≤` is compatible with `×` on the left, i.e. the induced order on `RV/Kˣ` is a translation-invariant order -/ def leMulCompat : LRV.Sentence :=
  allSorted ![.rv, .rv, .rv] (pRV &0 ⟹ (pRV &1 ⟹ (pRV &2 ⟹ (pUnits &2 ⟹ (pLe (&0) &1 ⟹ pLe (tRVMul (&0) &2) (tRVMul (&1) &2))))))
/-- Definition 2.2 item 4: `≤` is a preorder on `RV` with `∞` the top element and `Kˣ` the equivalence class of `1`. -/ def preorderRV : LRV.Theory :=
  ofList [leRefl, leTrans, leTotal, leTop, leInftyEq, leClassOne, leMulCompat]
/-- `rv(0) = ∞` -/ def rvZeroEq : LRV.Sentence :=
  pEq (tRv tVFZero) tRVInfty
/-- `rv(x) = ∞` forces `x = 0` -/ def rvEqInfty : LRV.Sentence :=
  allSorted ![.vf] (pEq (tRv &0) tRVInfty ⟹ pEq (&0) tVFZero)
/-- `rv` is a group homomorphism on `VF^×` -/ def rvMulHom : LRV.Sentence :=
  allSorted ![.vf, .vf] (pEq (tRv (tVFMul (&0) &1)) (tRVMul (tRv &0) (tRv &1)))
/-- **`rv` is surjective**: every element of the `RV` sort other than `rv(0)` is `rv(x)` for some `x ∈ VF`. (Definition 2.2(6): `rv : VF^× → RV^×` is surjective, augmented by `rv(0) = ∞ = 0`. With `RV^× = RV ∖ {0}` this says: `RV = rv(VF^×) ∪ {0}`, so there are no `RV`-elements outside the image of `rv`.) -/ def rvSurj : LRV.Sentence :=
  allSorted ![.rv] (∼(pEq (&0) tRVZero) ⟹ exSorted .vf (pEq (tRv &1) &0))
/-- the ultrametric inequality for `vv = vrv ∘ rv`: `vv(x+y) ≥ min(vv x, vv y)` -/ def rvUltrametric : LRV.Sentence :=
  allSorted ![.vf, .vf] (pLe (tRv &0) (tRv (tVFAdd (&0) &1)) ⊔ pLe (tRv &1) (tRv (tVFAdd (&0) &1)))
/-- Definition 2.2 item 6: `rv : VF^× → RV^×` is a surjective group homomorphism augmented by `rv(0) = ∞`, and `vv = vrv ∘ rv` is a valuation. (The valuation ring `O = rv⁻¹(RV^{≥1})` and the maximal ideal `M = rv⁻¹(RV^{>1})` are *defined* from `rv`, so — exactly as in the paper — they need no symbols of their own.) -/ def rvAxioms : LRV.Theory :=
  ofList [rvZeroEq, rvEqInfty, rvMulHom, rvSurj, rvUltrametric]
/-- `1` is neutral for `×` on every nonzero `RV`-element. -/ def rvMulOneRV : LRV.Sentence :=
  allSorted ![.rv] (pRV &0 ⟹ pEq (tRVMul tRVOne &0) &0)
/-- every nonzero `RV`-element is invertible in `RV^×`. -/ def rvMulInvRV : LRV.Sentence :=
  allSorted ![.rv] (pRV &0 ⟹ exSorted .rv (pRV &1 ⊓ pEq (tRVMul (&1) &0) tRVOne))
/-- the order on `RV` is invariant under scaling by any `c ≠ rv 0`, in both directions. The guards on the first two variables are dropped because `∞ = rv 0` is absorbing and top, so both sides hold there. -/ def leMulCompatFull : LRV.Sentence :=
  allSorted ![.rv, .rv, .rv] (pRV &2 ⟹ (pLe (&0) &1 ⇔ pLe (tRVMul (&0) &2) (tRVMul (&1) &2)))
/-- `kAdd` is the residue addition at units: `rv (x + y)` if that is a unit, and `0` if `x + y` drops into the maximal ideal. -/ def kAddLink : LRV.Sentence :=
  allSorted ![.vf, .vf] (pUnits (tRv &0) ⟹ (pUnits (tRv &1) ⟹ ((pUnits (tRv (tVFAdd (&0) &1)) ⟹ pEq (tKAdd (tRv &0) (tRv &1)) (tRv (tVFAdd (&0) &1))) ⊓ (∼(pUnits (tRv (tVFAdd (&0) &1))) ⟹ pEq (tKAdd (tRv &0) (tRv &1)) tRVZero))))
/-- `kNeg` is the residue negation at units. -/ def kNegLink : LRV.Sentence :=
  allSorted ![.vf] (pUnits (tRv &0) ⟹ pEq (tKNeg (tRv &0)) (tRv (tVFNeg &0)))
/-- two elements of `VF` have the same residue iff their difference has strictly larger value than the second: `rv a = rv b ↔ ¬ (v (a - b) ≤ v b)`. (The first transcription had the two `pLe` arguments transposed, which made the axiom false at `a = b = 1` and the whole theory inconsistent — see `QE-PLAN.md` and `.ultramath/smw163dd5/m5/Audit.lean`.) -/ def rvEqLink : LRV.Sentence :=
  allSorted ![.vf, .vf] (∼(pEq (&1) tVFZero) ⟹ (pEq (tRv &0) (tRv &1) ⇔ ∼(pLe (tRv (tVFAdd (&0) (tVFNeg &1))) (tRv &1))))
/-- the junk convention for `kAdd` off `K`: the value is `0`. -/ def kJunkZero : LRV.Sentence :=
  allSorted ![.rv, .rv] ((∼(pInK &0) ⊔ ∼(pInK &1)) ⟹ pEq (tKAdd (&0) &1) tRVZero)
/-- the junk convention for `kNeg` off `K`. -/ def kNegJunkZero : LRV.Sentence :=
  allSorted ![.rv] (∼(pInK &0) ⟹ pEq (tKNeg &0) tRVZero)
/-- **Nontriviality**: some nonzero element of `VF` has value strictly below the value of `1`, i.e. lies in the maximal ideal. -/ def axNontrivialRV : LRV.Sentence :=
  exSorted .vf (∼(pEq (&0) tVFZero) ⊓ ∼(pLe (tRv &0) (tRv tVFOne)))
/-- The inverse operation fixes the absorbing element `0 = ∞`. -/ def rvInvZero : LRV.Sentence :=
  pEq (tRVInv tRVZero) tRVZero
/-- The named inverse is a multiplicative inverse on the nonzero `RV` group. -/ def rvInvMul : LRV.Sentence :=
  allSorted ![.rv] (pRV &0 ⟹ pEq (tRVMul (tRVInv &0) &0) tRVOne)
/-- The added axioms, in one theory. -/ def repairRV : LRV.Theory :=
  ofList [rvMulOneRV, rvMulInvRV, leMulCompatFull, kAddLink, kNegLink, rvEqLink, kJunkZero, kNegJunkZero, axNontrivialRV, rvInvZero, rvInvMul]
/-- the paper's own content of `ACVF`: Definition 2.2, items 1–6 -/ def ACVFpaper : LRV.Theory :=
  vfField ∪ vfAlgClosed ∪ rvGroup ∪ kField ∪ kAlgClosed ∪ preorderRV ∪ rvAxioms ∪ repairRV ∪ repairRV
/-- **The theory `ACVF` of Definition 2.2**, in the tagged encoding: items 1–6 plus the sort discipline of the encoding. -/ def ACVF : LRV.Theory :=
  sortAxioms ∪ ACVFpaper
/-- characteristic zero of the `VF` sort -/ def charZeroVF (k : ℕ) : LRV.Sentence :=
  ∼(pEq (tVFNumeral (k + 1)) tVFZero)
/-- residue characteristic zero: for each prime `p`, `p · 1` is a unit of the valuation ring, i.e. `¬ (1 < rv(p·1))` -/ def residueCharZero (p : ℕ) : LRV.Sentence :=
  ∼(pGtOne (tRv (tVFNumeral p)))
/-- **The theory `ACVF(0,0)`**: `ACVF` with pure characteristic `0`, i.e. characteristic `0` for the valued field and characteristic `0` for its residue field. -/ def ACVF00 : LRV.Theory :=
  ACVF ∪ {s | ∃ k, s = charZeroVF k} ∪ {s | ∃ p, p.Prime ∧ s = residueCharZero p}
end Axioms namespace Gamma open Axioms LRV end Gamma namespace SubstructureTheory open Axioms end SubstructureTheory open Axioms open LRV
/-- Whether an element of a model has a given sort. -/ def sortEval {M : Type*} [LRV.Structure M] : SortTag → M → Prop
  | .vf => fun x => Structure.RelMap (L := LRV) Rel.memVF ![x]
  | .rv => fun x => Structure.RelMap (L := LRV) Rel.memRV ![x]
variable {M : Type*} [LRV.Structure M]
/-- `x` lies in the `VF` sort -/ def iVF (x : M) : Prop :=
  FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memVF ![x]
/-- `x` lies in the `RV` sort -/ def iRV (x : M) : Prop :=
  FirstOrder.Language.Structure.RelMap (L := LRV) Rel.memRV ![x]
/-- the preorder `≤` of the `RV` sort -/ def iLe (x y : M) : Prop :=
  FirstOrder.Language.Structure.RelMap (L := LRV) Rel.rvLe ![x, y]
/-- the interpretation of `+` of the `VF` sort -/ def iVFAdd (x y : M) : M :=
  FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfAdd ![x, y]
/-- the interpretation of `-` of the `VF` sort -/ def iVFNeg (x : M) : M :=
  FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfNeg ![x]
/-- the interpretation of `×` of the `VF` sort -/ def iVFMul (x y : M) : M :=
  FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfMul ![x, y]
/-- the interpretation of the projection `rv : VF → RV` -/ def iRv (x : M) : M :=
  FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvMap ![x]
/-- the interpretation of `0` of the `RV` sort -/ def iRVZero : M :=
  FirstOrder.Language.Structure.funMap (L := LRV) Fn.rvZero fun i => i.elim0
namespace Audit open LRV Axioms end Audit namespace Downstream end Downstream end Milestone0 end SpecialTransformations end end
reset_statement_module_caches section @[expose] public section open FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV namespace SpecialTransformations.Section3 variable {M : Type} [LRV.Structure M]
def FinitelySatisfiable {α : Type} {n : ℕ} (v : α → M) (p : Set (LRV.BoundedFormula α n)) : Prop :=
  ∀ l : List (LRV.BoundedFormula α n), (∀ φ ∈ l, φ ∈ p) → ∃ x : Fin n → M, ∀ φ ∈ l, φ.Realize v x
def Saturated (M : Type) [LRV.Structure M] (κ : Cardinal) : Prop :=
  ∀ (α : Type) (v : α → M), Cardinal.mk α < κ → ∀ {n : ℕ} (p : Set (LRV.BoundedFormula α n)), FinitelySatisfiable v p → ∃ x : Fin n → M, ∀ φ ∈ p, φ.Realize v x
end SpecialTransformations.Section3 end end
reset_statement_module_caches section @[expose] public section open Classical open FirstOrder FirstOrder.Language open scoped FirstOrder open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV namespace SpecialTransformations.Milestone0.Transfer
/-- `0` of the `VF` sort -/ def iVFZero {M : Type} [LRV.Structure M] : M :=
  FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfZero fun i => i.elim0
/-- `1` of the `VF` sort -/ def iVFOne {M : Type} [LRV.Structure M] : M :=
  FirstOrder.Language.Structure.funMap (L := LRV) Fn.vfOne fun i => i.elim0
end SpecialTransformations.Milestone0.Transfer namespace TrivCase open SpecialTransformations.Milestone0.Transfer end TrivCase namespace RVElim end RVElim
set_option linter.unusedSimpArgs false
open FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV namespace SpecialTransformations.Milestone0.Transfer namespace QFRes2 namespace VFT2 end VFT2 namespace RVT2 end RVT2 namespace VFT2 end VFT2 namespace RVT2 end RVT2 namespace VFT2 end VFT2 namespace RVT2 end RVT2 end QFRes2 end SpecialTransformations.Milestone0.Transfer open FirstOrder FirstOrder.Language open scoped FirstOrder open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV namespace SpecialTransformations.Milestone0.Transfer namespace QFRes2 namespace QF2 section Semantics end Semantics section Semantics end Semantics end QF2 end QFRes2 end SpecialTransformations.Milestone0.Transfer open FirstOrder FirstOrder.Language open scoped FirstOrder open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV namespace SpecialTransformations.Milestone0.Transfer namespace QFRes2 namespace QF2 end QF2 namespace QFq2 end QFq2 end QFRes2 end SpecialTransformations.Milestone0.Transfer namespace SpecialTransformations.Milestone0.Transfer variable {M : Type} [LRV.Structure M]
theorem rv_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M} (hx : iVF x) :
    iRV (iRv x)  := by sorry
theorem rv_zero_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iRV (iRVZero (M := M))  := by sorry
end SpecialTransformations.Milestone0.Transfer namespace SpecialTransformations.Milestone0.Transfer end SpecialTransformations.Milestone0.Transfer namespace SpecialTransformations.Milestone0.Transfer variable {M : Type} [LRV.Structure M] end SpecialTransformations.Milestone0.Transfer namespace SpecialTransformations.Milestone0.Transfer variable {M : Type} [LRV.Structure M]
theorem vf_zero_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iVF (iVFZero (M := M))  := by sorry
theorem vf_one_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iVF (iVFOne (M := M))  := by sorry
theorem vf_add_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) : iVF (iVFAdd x y)  := by sorry
theorem vf_neg_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : iVF (iVFNeg x)  := by sorry
theorem vf_mul_mem {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) : iVF (iVFMul x y)  := by sorry
end SpecialTransformations.Milestone0.Transfer namespace SpecialTransformations.Milestone0.Transfer.QFRes2 open SpecialTransformations.Milestone0.Transfer end SpecialTransformations.Milestone0.Transfer.QFRes2 end end
reset_statement_module_caches section @[expose] public section open FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 namespace SpecialTransformations.Milestone0 namespace RVCalc variable {M : Type} [LRV.Structure M] open LRV open SpecialTransformations.Milestone0.Transfer
/-- `≤` is reflexive at every `RV`-element (`leRefl` is guarded by `≠ 0`; at `0` the statement is the ultrametric axiom at `(0,0)` together with `rv 0 = 0`). -/ theorem le_refl_rv (hM : M ⊨ Axioms.ACVF) {a : M} (ha : iRV a) : iLe a a  := by sorry
theorem le_trans_rv (hM : M ⊨ Axioms.ACVF) {a b c : M} (ha : iRV a) (hb : iRV b) (hc : iRV c)
    (hab : iLe a b) (hbc : iLe b c) : iLe a c  := by sorry
end RVCalc end SpecialTransformations.Milestone0 end end
reset_statement_module_caches section @[expose] public section open FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 open SpecialTransformations.Milestone0.LRV namespace SpecialTransformations.Milestone0 namespace Transfer
theorem vf_add_assoc {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y z : M}
    (hx : iVF x) (hy : iVF y) (hz : iVF z) :
    iVFAdd (iVFAdd x y) z = iVFAdd x (iVFAdd y z)  := by sorry
theorem vf_add_comm {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) : iVFAdd x y = iVFAdd y x  := by sorry
theorem vf_add_zero {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : iVFAdd x iVFZero = x  := by sorry
theorem vf_add_neg {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : iVFAdd x (iVFNeg x) = iVFZero  := by sorry
theorem vf_mul_assoc {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y z : M}
    (hx : iVF x) (hy : iVF y) (hz : iVF z) :
    iVFMul (iVFMul x y) z = iVFMul x (iVFMul y z)  := by sorry
theorem vf_mul_comm {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y : M}
    (hx : iVF x) (hy : iVF y) : iVFMul x y = iVFMul y x  := by sorry
theorem vf_mul_one {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : iVFMul x iVFOne = x  := by sorry
theorem vf_left_distrib {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x y z : M}
    (hx : iVF x) (hy : iVF y) (hz : iVF z) :
    iVFMul x (iVFAdd y z) = iVFAdd (iVFMul x y) (iVFMul x z)  := by sorry
/-- `0 ≠ 1` on the `VF` sort. -/ theorem vf_zero_ne_one {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) :
    iVFZero (M := M) ≠ iVFOne  := by sorry
/-- **The invertibility law**: a `VF`-element is `0` or has a multiplicative inverse. The encoding states it this way because the language has no inverse symbol. -/ theorem vf_mul_inv_or_zero {M : Type} [LRV.Structure M] (hM : M ⊨ Axioms.ACVF) {x : M}
    (hx : iVF x) : x = iVFZero ∨ ∃ y : M, iVF y ∧ iVFMul x y = iVFOne  := by sorry
section VFField variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- The `VF` sort of an `ACVF`-model, as a type. -/ def VFType : Type :=
  { x : M // iVF x }
instance vfInstZero : Zero (VFType (M := M)) :=
  ⟨⟨iVFZero, vf_zero_mem hM⟩⟩
instance vfInstOne : One (VFType (M := M)) :=
  ⟨⟨iVFOne, vf_one_mem hM⟩⟩
instance vfInstAdd : Add (VFType (M := M)) :=
  ⟨fun x y => ⟨iVFAdd x.1 y.1, vf_add_mem hM x.2 y.2⟩⟩
instance vfInstNeg : Neg (VFType (M := M)) :=
  ⟨fun x => ⟨iVFNeg x.1, vf_neg_mem hM x.2⟩⟩
instance vfInstMul : Mul (VFType (M := M)) :=
  ⟨fun x y => ⟨iVFMul x.1 y.1, vf_mul_mem hM x.2 y.2⟩⟩
/-- The inverse on the `VF` sort: `0⁻¹ = 0`, and a nonzero element inverts by the invertibility law. -/ noncomputable def vfInvFun (x : VFType (M := M)) : VFType (M := M) := by
  classical
    exact
    if h : x.1 = iVFZero then 0
    else
      let w := (vf_mul_inv_or_zero hM x.2).resolve_left h
      ⟨Classical.choose w, (Classical.choose_spec w).1⟩
noncomputable instance vfInstInv : Inv (VFType (M := M)) :=
  ⟨vfInvFun⟩
theorem vfInv_zero : (0 : VFType (M := M))⁻¹ = 0 := by sorry
theorem vfInv_val {x : VFType (M := M)} (hx : x ≠ 0) : iVFMul x.1 ((x⁻¹ : VFType (M := M))).1 = iVFOne := by sorry
/-- **The `VF` sort is a field.** -/ noncomputable def vfFieldOfModel : Field (VFType (M := M)) :=
  Field.ofMinimalAxioms (VFType (M := M)) (fun a b c => Subtype.ext (vf_add_assoc hM a.2 b.2 c.2))
    (fun a =>
      Subtype.ext
        (by
          show iVFAdd iVFZero a.1 = a.1
          rw [vf_add_comm hM (vf_zero_mem hM) a.2]
          exact vf_add_zero hM a.2))
    (fun a =>
      Subtype.ext
        (by
          show iVFAdd (iVFNeg a.1) a.1 = iVFZero
          rw [vf_add_comm hM (vf_neg_mem hM a.2) a.2]
          exact vf_add_neg hM a.2))
    (fun a b c => Subtype.ext (vf_mul_assoc hM a.2 b.2 c.2)) (fun a b => Subtype.ext (vf_mul_comm hM a.2 b.2))
    (fun a =>
      Subtype.ext
        (by
          show iVFMul iVFOne a.1 = a.1
          rw [vf_mul_comm hM (vf_one_mem hM) a.2]
          exact vf_mul_one hM a.2))
    (fun a ha => Subtype.ext (vfInv_val ha)) vfInv_zero (fun a b c => Subtype.ext (vf_left_distrib hM a.2 b.2 c.2)) ⟨0, 1, fun h => vf_zero_ne_one hM (congrArg Subtype.val h)⟩
end VFField end Transfer end SpecialTransformations.Milestone0 end end
reset_statement_module_caches section @[expose] public section open FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 open SpecialTransformations.Milestone0.LRV namespace SpecialTransformations.Milestone0.VFValued section Model variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- The `Field` structure on the `VF` sort, as an instance, so that `IsValPred`'s `CommRing` requirement is discharged by typeclass search. -/ noncomputable instance instFieldVFType : Field (Transfer.VFType (M := M)) :=
  Transfer.vfFieldOfModel (M := M) (hM := hM)
/-- The paper's `v x ≤ v y` on the `VF` sort: `iLe (rv y) (rv x)`. -/ def predV (x y : Transfer.VFType (M := M)) : Prop :=
  iLe (iRv y.1) (iRv x.1)
/-- **Every model of the frozen `ACVF` carries a genuine Mathlib valuation on its `VF` sort**, and `predV` is that valuation's order: `iLe (rv y) (rv x) ↔ w x ≤ w y`. -/ theorem exists_valuation_predV : ∃ (Γ : Type) (_ : LinearOrderedCommGroupWithZero Γ) (w : Valuation (Transfer.VFType (M := M)) Γ), ∀ x y : Transfer.VFType (M := M), predV x y ↔ w x ≤ w y := by sorry
end Model end SpecialTransformations.Milestone0.VFValued end end
reset_statement_module_caches section @[expose] public section open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 open SpecialTransformations.Milestone0.LRV namespace CanonicalStructure variable {M : Type} [sM : LRV.Structure M]
def sortZero (s : SortTag) : M :=
  match s with
  | .vf => Transfer.iVFZero
  | .rv => iRVZero
/-- Correctly sorted applications retain their original interpretation. Wrong-sort applications return the named zero of the result sort. -/ @[instance_reducible]
noncomputable def normalize : LRV.Structure M where
  funMap f xs := if ∀ i, sortEval (Fn.argSort f i) (xs i) then Structure.funMap (L := LRV) f xs else sortZero (Fn.resSort f)
  RelMap r
    xs :=
    match r with
    | .memVF => Structure.RelMap (L := LRV) Rel.memVF xs
    | .memRV => Structure.RelMap (L := LRV) Rel.memRV xs
    | .memUnits => Structure.RelMap (L := LRV) Rel.memUnits xs
    | .rvLe => (∀ i, sortEval .rv (xs i)) ∧ Structure.RelMap (L := LRV) Rel.rvLe xs
section Soundness
variable (hM : M ⊨ Axioms.ACVF)
include hM
end Soundness section Formulas
variable (hM : M ⊨ Axioms.ACVF)
include hM
end Formulas end CanonicalStructure end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer namespace CanonicalRV
noncomputable def equivOfSameFibers {A B C : Type*} (f : A → B) (g : A → C) (hf : Function.Surjective f) (hg : Function.Surjective g) (h : ∀ a b, f a = f b ↔ g a = g b) : B ≃ C where
  toFun b := g (Classical.choose (hf b))
  invFun c := f (Classical.choose (hg c))
  left_inv
    b := by
    have he := Classical.choose_spec (hg (g (Classical.choose (hf b))))
    exact ((h _ _).mpr he).trans (Classical.choose_spec (hf b))
  right_inv
    c := by
    have he := Classical.choose_spec (hf (f (Classical.choose (hg c))))
    exact ((h _ _).mp he).trans (Classical.choose_spec (hg c))
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
abbrev RVSort (M : Type) [LRV.Structure M] :=
  { x : M // iRV x }
def encodedRv (a : VFType (M := M)) : RVSort M :=
  ⟨iRv a.1, rv_mem hM a.2⟩
theorem encodedRv_surjective : Function.Surjective (encodedRv (M := M)) := by sorry
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (v : Valuation (VFType (M := M)) Γ) (hv : ∀ a b : VFType (M := M), VFValued.predV a b ↔ v a ≤ v b)
include hv
end CanonicalRV end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer namespace SpecialTransformations.Section3.Values variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- Equality of values, rather than equality of RV classes. -/ def sameValue (x y : CanonicalRV.RVSort M) : Prop :=
  iLe x.val y.val ∧ iLe y.val x.val
def valueSetoid : Setoid (CanonicalRV.RVSort M) where
  r := sameValue
  iseqv := ⟨fun x => ⟨RVCalc.le_refl_rv hM x.property, RVCalc.le_refl_rv hM x.property⟩, fun h => ⟨h.2, h.1⟩, fun {x y z} hxy hyz => ⟨RVCalc.le_trans_rv hM x.property y.property z.property hxy.1 hyz.1, RVCalc.le_trans_rv hM z.property y.property x.property hyz.2 hxy.2⟩⟩
/-- The actual imaginary quotient, including its one infinity class. Ordered-group operations are not asserted by this definition alone. -/ def GammaTop :=
  Quotient (valueSetoid (M := M))
def vrv (t : CanonicalRV.RVSort M) : GammaTop (M := M) :=
  Quotient.mk _ t
def infinity : GammaTop (M := M) :=
  vrv ⟨iRVZero, rv_zero_mem hM⟩
theorem vrv_surjective : Function.Surjective (vrv (M := M)) := by sorry
theorem vrv_eq_infinity_iff (t : CanonicalRV.RVSort M) : vrv t = infinity (M := M) ↔ t.val = iRVZero := by sorry
/-- The genuine value-group carrier excludes the absorbing infinity class. -/ def Gamma :=
  { γ : GammaTop (M := M) // γ ≠ infinity }
theorem vf_value_eq_iff {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (v : Valuation (VFType (M := M)) Γ) (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y) (x y : VFType (M := M)) : vrv (CanonicalRV.encodedRv x) = vrv (CanonicalRV.encodedRv y) ↔ v x = v y := by sorry
end SpecialTransformations.Section3.Values end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer namespace SpecialTransformations.Section3.ClosedBallCodes variable {M : Type} [LRV.Structure M]
public def variableTerm (i : Fin 4) : LRV.Term (Fin 0 ⊕ Fin 4) :=
  .var (.inr i)
/-- The first coordinates are a center, a radius representative and a flag. Flag zero codes the whole field; any other flag codes the closed ball. -/ def body : LRV.BoundedFormula (Fin 0) 4 :=
  (.equal (variableTerm 2) (.func Fn.vfZero Fin.elim0)) ⊔ .rel Rel.rvLe ![.func Fn.rvMap ![variableTerm 1], .func Fn.rvMap ![.func Fn.vfAdd ![variableTerm 3, .func Fn.vfNeg ![variableTerm 0] ] ] ]
def tuple (t : Fin 3 → M) (x : M) : Fin 4 → M :=
  ![t 0, t 1, t 2, x]
def rawBall (t : Fin 3 → M) : Set M :=
  {x | (∀ i, iVF (t i)) ∧ iVF x ∧ body.Realize Fin.elim0 (tuple t x)}
variable [hM : M ⊨ Axioms.ACVF] end SpecialTransformations.Section3.ClosedBallCodes end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer namespace SpecialTransformations.Section3.ClosedBallCodes variable {M : Type} [LRV.Structure M]
/-- Real codes are identified precisely when their underlying balls agree. -/ def Code (M : Type) [LRV.Structure M] :=
  { t : Fin 3 → M // ∀ i, iVF (t i) }
def codeSetoid : Setoid (Code M) where
  r t u := rawBall t.val = rawBall u.val
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
abbrev ClosedBall (M : Type) [LRV.Structure M] :=
  Quotient (codeSetoid (M := M))
def underlying : ClosedBall M → Set M :=
  Quotient.lift (fun t : Code M => rawBall t.val) (fun _ _ h => h)
variable [hM : M ⊨ Axioms.ACVF] end SpecialTransformations.Section3.ClosedBallCodes namespace SpecialTransformations.Section3 end SpecialTransformations.Section3 end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV namespace SpecialTransformations.Section3.Values variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
def gammaOf (t : CanonicalRV.RVSort M) (ht : t.val ≠ iRVZero) : Gamma (M := M) :=
  ⟨vrv t, fun h => ht ((vrv_eq_infinity_iff t).mp h)⟩
def gammaPullback (V : Set (Gamma (M := M))) : Set M :=
  {t | ∃ hRV : iRV t, ∃ h0 : t ≠ iRVZero, gammaOf ⟨t, hRV⟩ h0 ∈ V}
end SpecialTransformations.Section3.Values namespace SpecialTransformations.Section3.RawValueFibres end SpecialTransformations.Section3.RawValueFibres end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer open MonoidWithZeroHom namespace SpecialTransformations.Section3.Values variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (v : Valuation (VFType (M := M)) Γ) (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
include hv
noncomputable def valueEquiv : GammaTop (M := M) ≃ ValueGroup₀ (.ofClass v) :=
  CanonicalRV.equivOfSameFibers (fun x : VFType (M := M) => vrv (CanonicalRV.encodedRv x)) v.restrict (vrv_surjective.comp CanonicalRV.encodedRv_surjective) (ValueGroup₀.restrict₀_surjective (.ofClass v)) (fun x y => (vf_value_eq_iff v hv x y).trans v.restrict_inj.symm)
end SpecialTransformations.Section3.Values end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer namespace SpecialTransformations.Section3.Values variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- An internal compatible valuation presentation. This makes no choice of RV representatives as parameters and does not extend the base S. -/ noncomputable def presentationType : Type :=
  Classical.choose (VFValued.exists_valuation_predV (M := M))
noncomputable instance presentationOrder : LinearOrderedCommGroupWithZero (presentationType (M := M)) :=
  Classical.choose (Classical.choose_spec (VFValued.exists_valuation_predV (M := M)))
noncomputable def presentationValuation : Valuation (VFType (M := M)) (presentationType (M := M)) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec (VFValued.exists_valuation_predV (M := M))))
theorem presentation_compatible (x y : VFType (M := M)) : VFValued.predV x y ↔ presentationValuation x ≤ presentationValuation y := by sorry
noncomputable def paperValueEquiv : GammaTop (M := M) ≃ OrderDual (MonoidWithZeroHom.ValueGroup₀ (.ofClass (presentationValuation (M := M)))) :=
  valueEquiv presentationValuation presentation_compatible
end SpecialTransformations.Section3.Values end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer namespace SpecialTransformations.Section3.Values variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- The zero of this group-with-zero is the paper's infinity. Its order is reversed, so no ordered-group-with-zero instance asserting zero-minimality is introduced. The transfer follows Mathlib's Apache-2.0 Equiv transfer pattern in Algebra/GroupWithZero/TransferInstance.lean (Johannes Hoelzl) and uses Algebra/GroupWithZero/InjSurj.lean. -/ noncomputable instance gammaTopGroup : CommGroupWithZero (GammaTop (M := M)) := by
  let e := paperValueEquiv (M := M)
  letI := e.zero
  letI := e.one
  letI := e.mul
  letI := e.Inv
  letI := e.div
  letI := e.pow ℕ
  letI := e.pow ℤ
  apply e.injective.commGroupWithZero e <;> intros <;> exact e.apply_symm_apply _
noncomputable instance gammaTopOrder : LinearOrder (GammaTop (M := M)) := by classical exact (paperValueEquiv (M := M)).linearOrder
theorem infinity_eq_zero : infinity (M := M) = (0 : GammaTop (M := M)) := by sorry
noncomputable def gammaTopUnitsEquiv : Gamma (M := M) ≃ (GammaTop (M := M))ˣ where
  toFun γ := Units.mk0 γ.val (fun h => γ.property (h.trans infinity_eq_zero.symm))
  invFun u := ⟨u.val, fun h => Units.ne_zero u (h.trans infinity_eq_zero)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Units.ext rfl
/-- Gamma inherits the reversed order on its actual non-infinity subtype. -/ noncomputable instance gammaOrder : LinearOrder (Gamma (M := M)) :=
  inferInstanceAs (LinearOrder { γ : GammaTop (M := M) // γ ≠ infinity })
noncomputable instance gammaGroup : CommGroup (Gamma (M := M)) :=
  (gammaTopUnitsEquiv (M := M)).commGroup
end SpecialTransformations.Section3.Values end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer namespace SpecialTransformations.Section3.Values variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
theorem vf_value_zero : vrv (CanonicalRV.encodedRv (0 : VFType (M := M))) = (0 : GammaTop (M := M)) := by sorry
theorem vf_value_one : vrv (CanonicalRV.encodedRv (1 : VFType (M := M))) = (1 : GammaTop (M := M)) := by sorry
theorem vf_value_mul (x y : VFType (M := M)) : vrv (CanonicalRV.encodedRv (x * y)) = vrv (CanonicalRV.encodedRv x) * vrv (CanonicalRV.encodedRv y) := by sorry
noncomputable def vfValueHom : VFType (M := M) →*₀ GammaTop (M := M) where
  toFun x := vrv (CanonicalRV.encodedRv x)
  map_zero' := vf_value_zero
  map_one' := vf_value_one
  map_mul' := vf_value_mul
end SpecialTransformations.Section3.Values end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV namespace SpecialTransformations.Section3.GammaParameters open Values variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- Real codes for Gamma elements are all nonzero RV representatives. There is no chosen section in a parameter base. -/ def Code :=
  { t : CanonicalRV.RVSort M // t.val ≠ iRVZero }
def raw (t : Code (M := M)) : M :=
  t.val.val
def value (t : Code (M := M)) : Gamma (M := M) :=
  gammaOf t.val t.property
theorem value_surjective : Function.Surjective (value (M := M)) := by sorry
/-- Used only inside proofs of surjectivity and descent. Definability of objects with Gamma parameters must use all codes and their invariance. -/ noncomputable def representative (γ : Gamma (M := M)) : Code (M := M) :=
  Classical.choose (value_surjective γ)
def rawTuple {n : ℕ} (t : Fin n → Code (M := M)) : Fin n → M := fun i => raw (t i)
def values {n : ℕ} (t : Fin n → Code (M := M)) : Fin n → Gamma (M := M) := fun i => value (t i)
def Proper {n : ℕ} (a : Fin n → M) : Prop :=
  ∀ i, iRV (a i) ∧ a i ≠ iRVZero
noncomputable def representatives {n : ℕ} (γ : Fin n → Gamma (M := M)) : Fin n → Code (M := M) := fun i => representative (γ i)
end SpecialTransformations.Section3.GammaParameters end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV namespace SpecialTransformations.Section3.GammaParameters variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- A genuine first-order relation with Gamma inputs, represented by its full invariant preimage on nonzero RV codes. Definability uses the normalized released LRV structure; no representative is named in the real base S. -/ structure Relation (S : Set M) (k n : ℕ) (sn : Fin n → SortTag) where
  carrier : Set ((Fin k → M) × (Fin n → M))
  definable : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin k ⊕ Fin n) {z | (z ∘ Sum.inl, z ∘ Sum.inr) ∈ carrier}
  proper : ∀ p ∈ carrier, Proper p.1 ∧ ∀ i, sortEval (sn i) (p.2 i)
  invariant : ∀ t u : Fin k → Code (M := M), values t = values u → ∀ b : Fin n → M, (rawTuple t, b) ∈ carrier ↔ (rawTuple u, b) ∈ carrier
namespace Relation variable {S : Set M} {k n : ℕ} {sn : Fin n → SortTag}
def fibre (R : Relation S k n sn) (γ : Fin k → Values.Gamma (M := M)) : Set (Fin n → M) :=
  {b | (rawTuple (representatives γ), b) ∈ R.carrier}
end Relation
/-- Definability over a finite tuple of actual Gamma parameters. The relation has a full first-order invariant preimage, not a chosen section. -/ def DefinableWith (S : Set M) {k n : ℕ} (γ : Fin k → Values.Gamma (M := M)) (sn : Fin n → SortTag) (A : Set (Fin n → M)) : Prop :=
  ∃ R : Relation S k n sn, R.fibre γ = A
/-- A base in the real sorts together with its genuinely imaginary names. -/ structure Base where
  real : Set M
  gamma : Set (Values.Gamma (M := M))
def DefinableOverBase (B : Base (M := M)) {n : ℕ} (sn : Fin n → SortTag) (A : Set (Fin n → M)) : Prop :=
  ∃ k, ∃ γ : Fin k → Values.Gamma (M := M), (∀ i, γ i ∈ B.gamma) ∧ DefinableWith B.real γ sn A
def DefinableAtBase (B : Base (M := M)) (σ : SortTag) (A : Set M) : Prop :=
  DefinableOverBase B (fun _ : Fin 1 => σ) {z | z 0 ∈ A}
def DefinableClosureAtBase (B : Base (M := M)) (σ : SortTag) (b : M) : Prop :=
  DefinableAtBase B σ { b }
def GammaDefinableOverBase (B : Base (M := M)) (A : Set (Values.Gamma (M := M))) : Prop :=
  DefinableAtBase B .rv (Values.gammaPullback A)
def GammaDefinableClosureAtBase (B : Base (M := M)) (γ : Values.Gamma (M := M)) : Prop :=
  GammaDefinableOverBase B { γ }
/-- These are closure definitions, not assertions of the paper's exchange or generation conclusions. Their algebraic laws are separate obligations. -/ def closureBase (B : Base (M := M)) : Base (M := M) where
  real := {b | ∃ σ, DefinableClosureAtBase B σ b}
  gamma := {γ | GammaDefinableClosureAtBase B γ}
def VFGammaGeneratedBase (B : Base (M := M)) : Prop :=
  ∃ A : Set M, ∃ G : Set (Values.Gamma (M := M)), A ⊆ B.real ∧ G ⊆ B.gamma ∧ (∀ a ∈ A, iVF a) ∧ closureBase ⟨A, G⟩ = B
end SpecialTransformations.Section3.GammaParameters end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV namespace SpecialTransformations.Section3.GammaParameters variable {M : Type} [sM : LRV.Structure M]
def NonzeroRV (x : M) : Prop :=
  iRV x ∧ x ≠ iRVZero
variable [hM : M ⊨ Axioms.ACVF] end SpecialTransformations.Section3.GammaParameters end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV namespace SpecialTransformations.Section3 variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] namespace GammaParameters
/-- Total semantic decoding used only to state full real-code preimages. Definability is always asserted for the entire guarded relation, never for a fictitious first-order language structure on the Gamma carrier. -/ noncomputable def codeValue (a : M) : Values.Gamma (M := M) :=
  if h : NonzeroRV a then value ⟨⟨a, h.1⟩, h.2⟩ else 1
end GammaParameters end SpecialTransformations.Section3
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV namespace SpecialTransformations.ModelTheory end SpecialTransformations.ModelTheory namespace SpecialTransformations.Section3.GammaParameters.EndpointLogic open SpecialTransformations.ModelTheory end SpecialTransformations.Section3.GammaParameters.EndpointLogic
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV namespace SpecialTransformations.Section3.GammaParameters.EndpointLogic end SpecialTransformations.Section3.GammaParameters.EndpointLogic open Classical namespace SpecialTransformations.Section3 end SpecialTransformations.Section3 open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 namespace SpecialTransformations.Section3.RawClosure.Tuple end SpecialTransformations.Section3.RawClosure.Tuple
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV namespace SpecialTransformations.Section3.GammaParameters variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] namespace GammaRVFamily end GammaRVFamily end SpecialTransformations.Section3.GammaParameters
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV namespace SpecialTransformations.Section3.GammaParameters variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] end SpecialTransformations.Section3.GammaParameters
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV namespace SpecialTransformations.Section3 variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] end SpecialTransformations.Section3 namespace SpecialTransformations.Section3.GammaParameters.GammaRVFamily open SpecialTransformations.ModelTheory end SpecialTransformations.Section3.GammaParameters.GammaRVFamily
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV namespace SpecialTransformations.Section3.GammaParameters.GammaRVFamily end SpecialTransformations.Section3.GammaParameters.GammaRVFamily end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer namespace SpecialTransformations.Section3.OpenBallCodes variable {M : Type} [sM : LRV.Structure M]
public def variableTerm (i : Fin 3) : LRV.Term (Fin 0 ⊕ Fin 3) :=
  .var (.inr i)
/-- A strict disc is the negation of the reverse weak valuation comparison. The first two VF coordinates are its center and actual radius representative. -/ def body : LRV.BoundedFormula (Fin 0) 3 :=
  (.rel Rel.rvLe ![.func Fn.rvMap ![.func Fn.vfAdd ![variableTerm 2, .func Fn.vfNeg ![variableTerm 0] ] ], .func Fn.rvMap ![variableTerm 1] ] : LRV.BoundedFormula (Fin 0) 3).not
def tuple (q : Fin 2 → M) (x : M) : Fin 3 → M :=
  ![q 0, q 1, x]
def Proper (q : Fin 2 → M) : Prop :=
  (∀ i, iVF (q i)) ∧ q 1 ≠ iVFZero
def rawBall (q : Fin 2 → M) : Set M :=
  {x | Proper q ∧ iVF x ∧ body.Realize Fin.elim0 (tuple q x)}
variable [hM : M ⊨ Axioms.ACVF]
def Code (M : Type) [LRV.Structure M] :=
  { q : Fin 2 → M // Proper q }
def codeSetoid : Setoid (Code M) where
  r q u := rawBall q.val = rawBall u.val
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
abbrev OpenBall (M : Type) [LRV.Structure M] :=
  Quotient (codeSetoid (M := M))
def underlying : OpenBall M → Set M :=
  Quotient.lift (fun q : Code M => rawBall q.val) (fun _ _ h => h)
end SpecialTransformations.Section3.OpenBallCodes
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer namespace SpecialTransformations.Section3.OpenBallCodes variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] end SpecialTransformations.Section3.OpenBallCodes end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer namespace SpecialTransformations.Section3.BallImaginaries variable {M : Type} [sM : LRV.Structure M]
/-- The closed chart includes singleton and whole-field codes; the open chart contains proper strict discs. Equal point sets are identified across both charts as well as within each chart. -/ abbrev Chart (M : Type) [LRV.Structure M] :=
  ClosedBallCodes.ClosedBall M ⊕ OpenBallCodes.OpenBall M
def chartSet : Chart M → Set M :=
  Sum.elim ClosedBallCodes.underlying OpenBallCodes.underlying
def chartSetoid : Setoid (Chart M) where
  r c d := chartSet c = chartSet d
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
abbrev Ball (M : Type) [LRV.Structure M] :=
  Quotient (chartSetoid (M := M))
def ofClosed (D : ClosedBallCodes.ClosedBall M) : Ball M :=
  Quotient.mk _ (.inl D)
def ofOpen (D : OpenBallCodes.OpenBall M) : Ball M :=
  Quotient.mk _ (.inr D)
variable [hM : M ⊨ Axioms.ACVF] end SpecialTransformations.Section3.BallImaginaries
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer namespace SpecialTransformations.Section3.BallFamilies end SpecialTransformations.Section3.BallFamilies namespace SpecialTransformations.Section3.ClosedBallCodes open GammaParameters end SpecialTransformations.Section3.ClosedBallCodes namespace SpecialTransformations.Section3.OpenBallCodes open GammaParameters end SpecialTransformations.Section3.OpenBallCodes
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer namespace SpecialTransformations.Section3.ClosedBallCodes open GammaParameters end SpecialTransformations.Section3.ClosedBallCodes namespace SpecialTransformations.Section3.OpenBallCodes open GammaParameters end SpecialTransformations.Section3.OpenBallCodes
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer namespace SpecialTransformations.Section3.BallImaginaries open GammaParameters variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] end SpecialTransformations.Section3.BallImaginaries end end
reset_statement_module_caches section @[expose] public section open Set FirstOrder namespace IntegrationInACVF.Section3.ImaginaryFamilies
set_option backward.isDefEq.respectTransparency false
universe u v w w' w''
structure Presentation (M : Type w) (I : Type w') (κ : Type w'') where
  codes : Set (κ → M)
  decode : codes → I
  onto : Function.Surjective decode
variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M] variable {I : Type w'} {κ : Type w''} [Finite κ] namespace Presentation end Presentation open Presentation variable {p : Presentation M I κ} {Q : Set M} {T : Set I} {C P : I → Set M} end IntegrationInACVF.Section3.ImaginaryFamilies end end
reset_statement_module_caches section @[expose] public section open Set FirstOrder open IntegrationInACVF.Section3.ImaginaryFamilies namespace IntegrationInACVF.Section3.ImaginaryParameters
set_option backward.isDefEq.respectTransparency false
universe u v w w' w'' w₁ w₂ w₃ variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M] variable {I : Type w'} {κ : Type w''}
def tupleCodes (p : Presentation M I κ) (θ : Type w₁) : Set (θ × κ → M) :=
  {a | ∀ j, (fun c => a (j, c)) ∈ p.codes}
noncomputable def tuplePresentation (p : Presentation M I κ) (θ : Type w₁) : Presentation M (θ → I) (θ × κ) where
  codes := tupleCodes p θ
  decode q j := p.decode ⟨(fun c => q.val (j, c)), q.property j⟩
  onto := by
    intro a
    choose q hq using fun j => p.onto (a j)
    exact ⟨⟨fun (j, c) => (q j).val c, fun j => (q j).property⟩, funext hq⟩
/-- Full guarded preimage of a relation with a finite tuple of real outputs. -/ def vectorPullback (p : Presentation M I κ) {υ : Type w₂} (R : I → Set (υ → M)) : Set (κ ⊕ υ → M) :=
  {z | ∃ hz : z ∘ Sum.inl ∈ p.codes, z ∘ Sum.inr ∈ R (p.decode ⟨z ∘ Sum.inl, hz⟩)}
def WithTuple (p : Presentation M I κ) (Q : Set M) {θ : Type w₁} {υ : Type w₂} (a : θ → I) (A : Set (υ → M)) : Prop :=
  ∃ R : (θ → I) → Set (υ → M), Q.Definable L (vectorPullback (tuplePresentation p θ) R) ∧ R a = A
structure Base (M : Type w) (I : Type w') where
  real : Set M
  imaginary : Set I
/-- A formula uses a finite subset of the named imaginary elements. Its relation remains invariant on every code of each of those elements. -/ def OverBase (p : Presentation M I κ) (B : Base M I) {υ : Type w₂} (A : Set (υ → M)) : Prop :=
  ∃ F : Finset I, (∀ i ∈ F, i ∈ B.imaginary) ∧ WithTuple (L := L) p B.real (Subtype.val : F → I) A
variable [Finite κ] {p : Presentation M I κ} {Q : Set M} end IntegrationInACVF.Section3.ImaginaryParameters end end
reset_statement_module_caches section @[expose] public section open Set FirstOrder open IntegrationInACVF.Section3.ImaginaryFamilies open IntegrationInACVF.Section3.ImaginaryParameters namespace IntegrationInACVF.Section3.ImaginaryBaseImages
set_option backward.isDefEq.respectTransparency false
universe u v w w' w'' w₁ w₂ variable {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M] variable {I : Type w'} {κ : Type w''} {J : Type w₁} {η : Type w₂} variable {p : Presentation M I κ} {B : Base M I} {q : Presentation M J η}
def graphOn (A : Set M) (f : M → M) : Set (Fin 2 → M) :=
  {z | z 0 ∈ A ∧ z 1 = f (z 0)}
variable [Finite η] end IntegrationInACVF.Section3.ImaginaryBaseImages end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer open SpecialTransformations.Section3 open IntegrationInACVF.Section3 IntegrationInACVF.Section3.ImaginaryFamilies namespace IntegrationInACVF.Section3ACVF.BallPresentation variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
def closedTuple (q : Fin 4 → M) : Fin 3 → M :=
  ![q 0, q 1, q 2]
def openTuple (q : Fin 4 → M) : Fin 2 → M :=
  ![q 0, q 1]
def codeDomain : Set (Fin 4 → M) :=
  {q | (q 3 = iVFZero ∧ ∀ i, iVF (closedTuple q i)) ∨ (q 3 ≠ iVFZero ∧ OpenBallCodes.Proper (openTuple q))}
noncomputable def decode (q : codeDomain (M := M)) : BallImaginaries.Ball M :=
  if h : q.val 3 = iVFZero then BallImaginaries.ofClosed (Quotient.mk _ (⟨closedTuple q.val, (q.property.resolve_right (fun hn => hn.1 h)).2⟩ : ClosedBallCodes.Code M)) else BallImaginaries.ofOpen (Quotient.mk _ (⟨openTuple q.val, (q.property.resolve_left (fun hz => h hz.1)).2⟩ : OpenBallCodes.Code M))
end IntegrationInACVF.Section3ACVF.BallPresentation end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer open SpecialTransformations.Section3 SpecialTransformations.Section4 open IntegrationInACVF.Section3 IntegrationInACVF.Section3.ImaginaryFamilies open IntegrationInACVF.Section3ACVF.BallCosetAtomicity open IntegrationInACVF.Section3ACVF.NamedRadiusAtomicity namespace IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
public noncomputable def difference (x y : VFType (M := M)) : VFType (M := M) :=
  x - y
/-- A ball written using the actual Gamma value, in the paper's order. -/ def gammaBall (a : VFType (M := M)) (γ : Values.Gamma (M := M)) (strict : Bool) : Set M :=
  {x | ∃ hx : iVF x, γ.val ≤ (@Values.vfValueHom M sM hM) ((@difference M sM hM) ⟨x, hx⟩ a) ∧ (strict = true → ¬(@Values.vfValueHom M sM hM) ((@difference M sM hM) ⟨x, hx⟩ a) ≤ γ.val)}
end IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters open IntegrationInACVF.Section3 IntegrationInACVF.Section3.ImaginaryFamilies namespace IntegrationInACVF.Section3ACVF.ParameterPresentation variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
abbrev Name :=
  BallImaginaries.Ball M ⊕ Values.Gamma (M := M)
def ballTuple (z : Fin 5 → M) : Fin 4 → M := fun j => z j.castSucc
def codeDomain : Set (Fin 5 → M) :=
  {z | (z 4 = iVFZero ∧ ballTuple z ∈ BallPresentation.codeDomain) ∨ (z 4 ≠ iVFZero ∧ NonzeroRV (z 0))}
noncomputable def decode (z : codeDomain (M := M)) : Name (M := M) :=
  if h : z.val 4 = iVFZero then Sum.inl (BallPresentation.decode ⟨ballTuple z.val, (z.property.resolve_right (fun hn => hn.1 h)).2⟩) else Sum.inr (codeValue (z.val 0))
theorem decode_surjective : Function.Surjective (decode (M := M)) := by sorry
noncomputable def presentation : Presentation M (Name (M := M)) (Fin 5) :=
  ⟨codeDomain, decode, decode_surjective⟩
end IntegrationInACVF.Section3ACVF.ParameterPresentation end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer open SpecialTransformations.Section3 open IntegrationInACVF.Section3 IntegrationInACVF.Section3.ImaginaryFamilies namespace IntegrationInACVF.Section3ACVF.FullBaseAtomicity variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
abbrev Base :=
  ImaginaryParameters.Base M (ParameterPresentation.Name (M := M))
abbrev OverBase (B : Base (M := M)) {α : Type} (A : Set (α → M)) : Prop :=
  @ImaginaryParameters.OverBase LRV M (CanonicalStructure.normalize (M := M)) (ParameterPresentation.Name (M := M)) (Fin 5) (@ParameterPresentation.presentation M sM hM) B α A
end IntegrationInACVF.Section3ACVF.FullBaseAtomicity end end
reset_statement_module_caches section @[expose] public section open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer open SpecialTransformations.Section3 open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity open IntegrationInACVF.Section3ACVF.PuncturedGeometry namespace IntegrationInACVF.Section3ACVF.PaperBalls variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- Definition 2.2 with the sequel's explicit whole-field convention. -/ def IsOpenBall (B : Set M) : Prop :=
  B = {x | iVF x} ∨ ∃ a : VFType (M := M), ∃ γ : Values.Gamma (M := M), B = gammaBall a γ true
abbrev Radius :=
  WithBot (Values.GammaTop (M := M))
/-- Radius is a property of the actual parent point set, with no selected centre or representative included in the data. -/ def HasRadius (B : Set M) (r : Radius (M := M)) : Prop :=
  (B = {x | iVF x} ∧ r = ⊥) ∨ (∃ a : VFType (M := M), B = { a.val } ∧ r = (↑(Values.infinity (M := M)) : Radius (M := M))) ∨ ∃ a : VFType (M := M), ∃ γ : Values.Gamma (M := M), ∃ strict : Bool, B = gammaBall a γ strict ∧ r = (↑γ.val : Radius (M := M))
end IntegrationInACVF.Section3ACVF.PaperBalls end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters open SpecialTransformations.Section4 open IntegrationInACVF.Section3 namespace IntegrationInACVF.Section3ACVF.FullGammaSyntax variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
def Scalar (B : FullBaseAtomicity.Base (M := M)) (A : Set (Values.Gamma (M := M))) : Prop :=
  FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ Values.gammaPullback A}
variable {ι υ : Type} [Finite ι] [Finite υ] {B : FullBaseAtomicity.Base (M := M)} end IntegrationInACVF.Section3ACVF.FullGammaSyntax end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity open IntegrationInACVF.Section3ACVF.PuncturedGeometry open IntegrationInACVF.Section3ACVF.CanonicalBallSupport open IntegrationInACVF.Section3ACVF.ThinFamilyGeometry namespace IntegrationInACVF.Section3ACVF.MaximalOpenClasses variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
def OpenToOpen (A : Set M) (f : M → M) : Prop :=
  ∀ D ⊆ A, PaperBalls.IsOpenBall D ↔ PaperBalls.IsOpenBall (f '' D)
end IntegrationInACVF.Section3ACVF.MaximalOpenClasses end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
open Set Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 open IntegrationInACVF.Section3 namespace IntegrationInACVF.Section3ACVF.FullOpenToOpenPartition variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
theorem proposition_3_19 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A C : Set M} (hA : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ A})
    (hAVF : A ⊆ {x | iVF x}) (hCVF : C ⊆ {x | iVF x})
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hbij : Set.BijOn f A C) :
    ∃ P : Finset (Set M),
      (∀ U ∈ P, U.Nonempty ∧ U ⊆ A ∧
        FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ U} ∧
        MaximalOpenClasses.OpenToOpen U f) ∧
      (P : Set (Set M)).Pairwise Disjoint ∧ A = {x | ∃ U ∈ P, x ∈ U}  := by sorry
end IntegrationInACVF.Section3ACVF.FullOpenToOpenPartition end end
reset_statement_module_caches section @[expose] public section
set_option backward.isDefEq.respectTransparency false
open Set Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 open IntegrationInACVF.Section3 open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity open IntegrationInACVF.Section3ACVF.GammaTailMap namespace IntegrationInACVF.Section3ACVF.GammaLinearity variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
def GammaLinear (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x)) (s : Values.Gamma (M := M)) : Prop :=
  ∀ (x y : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A),
    let fx : VFType (M := M) := ⟨f x.val, hfVF _ hx⟩
    let fy : VFType (M := M) := ⟨f y.val, hfVF _ hy⟩
    Values.vfValueHom (fy - fx) = s.val * Values.vfValueHom (y - x)
end IntegrationInACVF.Section3ACVF.GammaLinearity end end
reset_statement_module_caches section @[expose] public section open FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer namespace SpecialTransformations.Section5 variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
abbrev VF :=
  VFType (M := M)
abbrev RV :=
  { t : M // iRV t }
abbrev Point (n m : ℕ) :=
  (Fin n → VF (M := M)) × (Fin m → RV (M := M))
def rv (x : VF (M := M)) : RV (M := M) :=
  ⟨iRv x.val, rv_mem hM x.property⟩
end SpecialTransformations.Section5 end end
reset_statement_module_caches section @[expose] public section noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer namespace SpecialTransformations.Section5 variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] namespace FocusGeometry end FocusGeometry namespace Focus end Focus namespace Primitive end Primitive end SpecialTransformations.Section5 namespace SpecialTransformations.Section5 variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] namespace FocusGeometry end FocusGeometry
/-- A typed coordinate accessor keeps the shared VF field instance visible when a point is carried by a definable presentation. -/ def vfAt {n m : ℕ} (p : Point (M := M) n m) (i : Fin n) : VF (M := M) :=
  p.1 i
namespace Primitive end Primitive namespace Chain end Chain namespace SpecialBijection end SpecialBijection end SpecialTransformations.Section5 end end end
reset_statement_module_caches section @[expose] public section noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV namespace SpecialTransformations.Section5 variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF] variable {S : Set M} {n m l : ℕ}
def gammaPointCode (p : Point (M := M) n m) : Fin (n + m) → M :=
  Fin.append (fun i => (vfAt p i).val) (fun i => (p.2 i).val)
def gammaPointSort (n m : ℕ) : Fin (n + m) → SortTag :=
  Fin.append (fun _ => .vf) (fun _ => .rv)
def GammaSetDefinable (B : Section3.GammaParameters.Base (M := M)) (A : Set (Point (M := M) n m)) : Prop :=
  Section3.GammaParameters.DefinableOverBase B (gammaPointSort n m) (gammaPointCode '' A)
def GammaGraphDefinable (B : Section3.GammaParameters.Base (M := M)) {u w : ℕ} (r : Point (M := M) n m → Point (M := M) u w → Prop) : Prop :=
  Section3.GammaParameters.DefinableOverBase B (Fin.append (gammaPointSort n m) (gammaPointSort u w)) {z | ∃ p q, r p q ∧ Fin.append (gammaPointCode p) (gammaPointCode q) = z}
end SpecialTransformations.Section5 end end end
reset_statement_module_caches section @[expose] public section noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF namespace IntegrationInACVF.Section4 variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- An actual finite-arity RV-valued function, with its complete graph definable over the unchanged original Gamma base. -/ structure GammaRVMap (G : GammaParameters.Base (M := M)) {n m : ℕ} (A : Set (Point (M := M) n m)) (d : ℕ) where
  toFun : A → Fin d → RV (M := M)
  graph : GammaGraphDefinable G (fun (p : Point (M := M) n m) (q : Point (M := M) 0 d) => ∃ a : A, a.val = p ∧ toFun a = q.2)
namespace GammaRVMap end GammaRVMap end IntegrationInACVF.Section4 end end end
reset_statement_module_caches section @[expose] public section noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF namespace IntegrationInACVF.Section4.RVLabelSlices variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
def labelBase (G : GammaParameters.Base (M := M)) {d : ℕ} (s : Fin d → RV (M := M)) : GammaParameters.Base (M := M) :=
  ⟨G.real ∪ Set.range (fun i => (s i).val), G.gamma⟩
end IntegrationInACVF.Section4.RVLabelSlices end end end
reset_statement_module_caches section @[expose] public section noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Section5 namespace IntegrationInACVF.Section4.BalancedFibres variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
def translatedRV (t : RV (M := M)) (c : VF (M := M)) : Set (VF (M := M)) :=
  {x | rv (x - c) = t}
def fibre (R : Set (VF (M := M) × VF (M := M))) (a : VF (M := M)) : Set (VF (M := M)) :=
  {b | (a, b) ∈ R}
structure HasBalancedFibres (D E : Set (VF (M := M))) (R : Set (VF (M := M) × VF (M := M))) (f : VF (M := M) → VF (M := M)) (t₁ t₂ : RV (M := M)) : Prop where
  bijective : Set.BijOn f D E
  subset : R ⊆ D ×ˢ E
  vertical : ∀ a ∈ D, fibre R a = translatedRV t₂ (f a)
  horizontal : ∀ a ∈ D, D ∩ f ⁻¹' fibre R a = {x | rv (a - x) = t₁}
variable {D E : Set (VF (M := M))} {R : Set (VF (M := M) × VF (M := M))} variable {f : VF (M := M) → VF (M := M)} {t₁ t₂ : RV (M := M)} end IntegrationInACVF.Section4.BalancedFibres end end end
reset_statement_module_caches section @[expose] public section noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 open SpecialTransformations.Section5 open IntegrationInACVF.Section3ACVF namespace IntegrationInACVF.Section4.Cells open BalancedFibres variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
def rawSet (D : Set (VF (M := M))) : Set M :=
  Subtype.val '' D
def rawMap (f : VF (M := M) → VF (M := M)) (x : M) : M :=
  if hx : iVF x then (f ⟨x, hx⟩).val else iVFZero
theorem rawMap_vf (f : VF (M := M) → VF (M := M)) (D : Set (VF (M := M))) : ∀ x ∈ rawSet D, iVF (rawMap f x) := by sorry
def first (R : Set (VF (M := M) × VF (M := M))) : Set (VF (M := M)) :=
  Prod.fst '' R
def second (R : Set (VF (M := M) × VF (M := M))) : Set (VF (M := M)) :=
  Prod.snd '' R
def IsOneCell (D : Set (VF (M := M))) : Prop :=
  (∃ x : VF (M := M), D = { x }) ∨ (PaperBalls.IsOpenBall (rawSet D) ∧ ∃ t : RV (M := M), ∀ x ∈ D, rv x = t)
def IsBalanced (R : Set (VF (M := M) × VF (M := M))) (f : VF (M := M) → VF (M := M)) (t₁ t₂ : RV (M := M)) : Prop :=
  PaperBalls.IsOpenBall (rawSet (first R)) ∧ PaperBalls.IsOpenBall (rawSet (second R)) ∧ HasBalancedFibres (first R) (second R) R f t₁ t₂ ∧ MaximalOpenClasses.OpenToOpen (rawSet (first R)) (rawMap f) ∧ ∃ s : Values.Gamma (M := M), GammaLinearity.GammaLinear (rawSet (first R)) (rawMap f) (rawMap_vf f (first R)) s
def PositioningCase (R : Set (VF (M := M) × VF (M := M))) (f : VF (M := M) → VF (M := M)) (t : RV (M := M)) : Prop :=
  (∀ a ∈ first R, ∀ b ∈ first R, f a = f b) ∨ (Set.InjOn f (first R) ∧ MaximalOpenClasses.OpenToOpen (rawSet (first R)) (rawMap f) ∧ ∃ r : PaperBalls.Radius (M := M), PaperBalls.HasRadius (rawSet (f '' first R)) r ∧ (↑(Values.vrv t) : PaperBalls.Radius (M := M)) ≤ r) ∨ ∃ t₁ : RV (M := M), IsBalanced R f t₁ t
structure CellData (R : Set (VF (M := M) × VF (M := M))) (position : VF (M := M) → VF (M := M)) (paradigm : RV (M := M)) : Prop where
  rv_polydisc : ∃ t₁ t₂ : RV (M := M), ∀ p ∈ R, rv p.1 = t₁ ∧ rv p.2 = t₂
  first_cell : IsOneCell (first R)
  fibres : ∀ a ∈ first R, fibre R a = translatedRV paradigm (position a)
  positioning : PositioningCase R position paradigm
def pairCodes (R : Set (VF (M := M) × VF (M := M))) : Set (Fin 2 → M) :=
  {z | ∃ p ∈ R, z = ![p.1.val, p.2.val]}
def positionCodes (D : Set (VF (M := M))) (position : VF (M := M) → VF (M := M)) : Set (Fin 2 → M) :=
  {z | ∃ a ∈ D, z = ![a.val, (position a).val]}
def DefinableCellData (G : GammaParameters.Base (M := M)) (R : Set (VF (M := M) × VF (M := M))) (position : VF (M := M) → VF (M := M)) (paradigm : RV (M := M)) : Prop :=
  CellData R position paradigm ∧ GammaParameters.DefinableOverBase G (fun _ : Fin 2 => .vf) (pairCodes R) ∧ GammaParameters.DefinableOverBase G (fun _ : Fin 2 => .vf) (positionCodes (first R) position) ∧ GammaParameters.DefinableAtBase G .rv { paradigm.val } ∧ (∀ t₁, IsBalanced R position t₁ paradigm → GammaParameters.DefinableAtBase G .rv { t₁.val })
def DefinableTwoCell (G : GammaParameters.Base (M := M)) (R : Set (VF (M := M) × VF (M := M))) : Prop :=
  ∃ position : VF (M := M) → VF (M := M), ∃ paradigm : RV (M := M), DefinableCellData G R position paradigm
end IntegrationInACVF.Section4.Cells end end end
reset_statement_module_caches section @[expose] public section noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF namespace IntegrationInACVF.Section4 variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
def pairPoint (a y : VF (M := M)) : Point (M := M) 2 0 :=
  (![y, a], Fin.elim0)
def GammaRVMap.pairFibre {G : GammaParameters.Base (M := M)} {d : ℕ} {A : Set (Point (M := M) 2 0)} (P : GammaRVMap G A d) (a₀ : A) : Set (VF (M := M) × VF (M := M)) :=
  {p | ∃ a : A, a.val = pairPoint p.1 p.2 ∧ P.toFun a = P.toFun a₀}
namespace VerticalPresentation end VerticalPresentation end IntegrationInACVF.Section4 end end end
reset_statement_module_caches section @[expose] public section noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Classical FirstOrder FirstOrder.Language open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3 open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5 open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF namespace IntegrationInACVF.Section4 variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
/-- Lemma 4.8. Every original-Gamma-base definable VF² set admits an actual finite-arity RV map over that same base. Every nonempty fibre is a two-cell, and its positioning graph and both paradigms are definable over its output RV tuple together with the original base. Native coordinate 1 is the first coordinate in the displayed pair fibre; no carrier or language is replaced. -/ theorem lemma_4_8 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (hGenerated : VFGammaGeneratedBase G)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ)
    (A : Set (Point (M := M) 2 0)) (hA : GammaSetDefinable G A) :
    ∃ d : ℕ, ∃ P : GammaRVMap G A d, ∀ a₀ : A,
      Cells.DefinableTwoCell (RVLabelSlices.labelBase G (P.toFun a₀)) (P.pairFibre a₀)  := by sorry
end IntegrationInACVF.Section4 end end end
