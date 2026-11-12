import IntegrationSection6.GammaRVSetRealization
import IntegrationSection6.GammaRVRestrictions
import Section5.GammaFiniteFibres
import Section3.SmallFiniteParameters

/-! Reconstruct actual finite Gamma RV objects from full domain/volume
relations and their functional/finite-fibre laws. The real presentation
adds only finitely many proper Gamma representatives to the original base.
This supports promotion of finite blowup witness schemata in6.14. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Section4.realSpace
  SpecialTransformations.Milestone0.sortEval SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)

structure GammaFiniteGraphPresentation (B : Base (M := M)) (a n : ℕ)
    (D : Set (Fin a → RV (M := M))) (R : (Fin a → RV (M := M)) → (Fin n → RV (M := M)) → Prop) where
  codes : Set M
  real_contains : B.real ⊆ codes
  finite_extra : ∃ F : Set M, F.Finite ∧ codes = B.real ∪ F
  domain : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@SpecialTransformations.Section4.rawRVSpace M N a) codes
  domain_eq : (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ codes domain) = D
  volume : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ codes domain
    (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N n) codes)
  graph_iff : ∀ x y, (∃ u : domain, u.val = x ∧ (volume u).val = y) ↔ x ∈ D ∧ R x y
  finite_volume : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M N _ _ codes _ _ volume
  domain_graph : GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ D}
  volume_graph : GammaGraphDefinable B (fun (p : Point (M := M) 0 a) (q : Point (M := M) 0 n) =>
    ∃ u : domain, u.val = p.2 ∧ (volume u).val = q.2)

variable {B : Base (M := M)} {a n : ℕ}
variable {D : Set (Fin a → RV (M := M))} {R : (Fin a → RV (M := M)) → (Fin n → RV (M := M)) → Prop}

def GammaFiniteGraphPresentation.toGamma (P : GammaFiniteGraphPresentation B a n D R) : GammaRVFiniteObject B n where
  codes := P.codes
  real_contains := P.real_contains
  object := @RVObject.mk M N P.codes n a P.domain P.volume
  domain_graph := by
    change GammaSetDefinable B {p : Point (M := M) 0 a |
      p.2 ∈ (@SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M N _ P.codes P.domain)}
    rw [P.domain_eq]
    exact P.domain_graph
  volume_graph := P.volume_graph
  finite_volume := P.finite_volume

theorem GammaFiniteGraphPresentation.codes_small (P : GammaFiniteGraphPresentation B a n D R)
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hsmall : Cardinal.mk B.real < κ) : Cardinal.mk P.codes < κ := by
  obtain ⟨F,hF,he⟩ := P.finite_extra
  rw [he]
  exact SpecialTransformations.Section3.small_union_finite hκ B.real hsmall F hF

theorem exists_gammaFiniteGraphPresentation
    (hD : GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ D})
    (hR : GammaGraphDefinable B (fun (p : Point (M := M) 0 a) (q : Point (M := M) 0 n) => R p.2 q.2))
    (hfunctional : ∀ x : D, ∃! y : Fin n → RV (M := M), R x.val y)
    (hfinite : ∀ y : Fin n → RV (M := M), {x : D | R x.val y}.Finite) :
    Nonempty (GammaFiniteGraphPresentation B a n D R) := by
  obtain ⟨d,t,hDr⟩ := gamma_rv_set_real_specialize D hD
  have hRR := (gammaLogicInput B).restrict_graph hD hR
  obtain ⟨e,u,hRr⟩ := gamma_rv_relation_real_specialize hRR
  let S := (B.real ∪ Set.range (rawTuple t)) ∪ (B.real ∪ Set.range (rawTuple u))
  have hDS : @SpecialTransformations.DefinableGeometry.Space.Definable LRV M N
      (@SpecialTransformations.Section4.rawRVSpace M N a) S D :=
    @SpecialTransformations.DefinableGeometry.Space.Definable.mono LRV M N
      (@SpecialTransformations.Section4.rawRVSpace M N a)
      (B.real ∪ Set.range (rawTuple t)) S D hDr Set.subset_union_left
  have hRS : @SpecialTransformations.DefinableGeometry.Space.RelationDefinable LRV M N
      (@SpecialTransformations.Section4.rawRVSpace M N a) (@SpecialTransformations.Section4.rawRVSpace M N n) S
      (fun x y => x ∈ D ∧ R x y) :=
    @SpecialTransformations.DefinableGeometry.Space.RelationDefinable.mono LRV M N
      (@SpecialTransformations.Section4.rawRVSpace M N a) (@SpecialTransformations.Section4.rawRVSpace M N n)
      (B.real ∪ Set.range (rawTuple u)) S _ hRr Set.subset_union_right
  let A : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@SpecialTransformations.Section4.rawRVSpace M N a) S :=
    @SpecialTransformations.DefinableGeometry.DefSet.mk LRV M N
      (@SpecialTransformations.Section4.rawRVSpace M N a) S D hDS
  let Q := @SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@SpecialTransformations.Section4.rawRVSpace M N n) S
  let f (x : A) : Q := ⟨(hfunctional ⟨x.val,x.property⟩).exists.choose,Set.mem_univ _⟩
  have hf (x : A) : R x.val (f x).val := (hfunctional ⟨x.val,x.property⟩).exists.choose_spec
  have hg (x y) : (x ∈ D ∧ R x y) ↔ ∃ z : A, z.val = x ∧ (f z).val = y := by
    constructor
    · rintro ⟨hx,hxy⟩
      exact ⟨⟨x,hx⟩,rfl,(hfunctional ⟨x,hx⟩).unique (hf ⟨x,hx⟩) hxy⟩
    · rintro ⟨z,rfl,rfl⟩
      exact ⟨z.property,hf z⟩
  have hfg := @SpecialTransformations.DefinableGeometry.Space.RelationDefinable.congr LRV M N
    (@SpecialTransformations.Section4.rawRVSpace M N a) (@SpecialTransformations.Section4.rawRVSpace M N n) S _ _ hRS hg
  let F := @SpecialTransformations.DefinableGeometry.Map.mk LRV M N _ _ S A Q f hfg
  have hFfinite : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M N _ _ S A Q F := by
    intro y
    apply (hfinite y.val).subset
    intro x hx
    exact (congrArg Subtype.val hx) ▸ hf x
  have hFΓ : GammaGraphDefinable B (fun (p : Point (M := M) 0 a) (q : Point (M := M) 0 n) =>
      ∃ x : A, x.val = p.2 ∧ (F x).val = q.2) := by
    apply GammaGraphDefinable.congr hRR
    intro p q
    exact hg p.2 q.2
  refine ⟨{
    codes := S
    real_contains := fun x hx => Or.inl (Or.inl hx)
    finite_extra := ?_
    domain := A
    domain_eq := rfl
    volume := F
    graph_iff := fun x y => (hg x y).symm
    finite_volume := hFfinite
    domain_graph := hD
    volume_graph := hFΓ }⟩
  refine ⟨Set.range (rawTuple t) ∪ Set.range (rawTuple u),(Set.finite_range _).union (Set.finite_range _),?_⟩
  simp only [S,Set.union_assoc,Set.union_left_comm,Set.union_self]
  rw [← Set.union_assoc,Set.union_self]

end IntegrationInACVF.Section6
