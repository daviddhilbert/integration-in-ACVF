import IntegrationSection6.PartialFamilyParameterPreservation
import IntegrationSection6.GammaMixedSetPresentations
import Section5.GammaFiniteFibres

/-! Every finite-RV-fibre mixed family has a uniform RV representative
whose total lift is isomorphic over its unchanged VF parameter base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p n a : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

structure RelativeFamilyRepresentation (B : Base (M := M)) (A : Set (Point (M := M) p 0))
    (W : Set (Point (M := M) (p+n) a)) where
  arity : ℕ
  schema : GammaFiniteRVSchema B p arity n
  finite : ∀ x : A, schema.finiteRow (fun j => (x.val.1 j).val)
  iso : GammaIso B W (familyLiftDomain A schema)
  parameters : ∀ u : W, ∀ j : Fin p,
    vfAt (iso.equiv u).val (Fin.castAdd n j) = vfAt u.val (Fin.castAdd n j)

theorem relativeFamilyRepresentation_exists {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ)
    (FBase : VFFieldBase B.real) (A : Set (Point (M := M) p 0))
    (W : Set (Point (M := M) (p+n) a)) (hW : GammaSetDefinable B W)
    (hfin : ∀ x : Fin (p+n) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ W}.Finite)
    (hWA : ∀ q ∈ W, (q.1 ∘ Fin.castAdd n,Fin.elim0) ∈ A) :
    Nonempty (RelativeFamilyRepresentation B A W) := by
  let e := gammaVFCoordinateIso W hW (activeFrozenShuffle p n)
  let D : Set (Point (M := M) (p+n) a) :=
    {q | (q.1 ∘ (activeFrozenShuffle p n).symm,q.2) ∈ W}
  have hD : GammaSetDefinable B D := e.target_definable (gammaLogicInput B)
  have hDfin : ∀ x : Fin (p+n) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ D}.Finite :=
    finiteRVFibres_of_gammaIso hκ hs B hr e
      (fun q _ => @vfTupleTrdeg_le_arity M N hN B.real (p+n) q.1) hfin
  let X := gammaMixedUniversalDefSet D hD
  obtain ⟨l,V,T,hT⟩ := gamma_partial_contraction_program hs h00 B hr FBase (Set.subset_univ _) p n X hD
  have hXA : ∀ u : X, (fun j => vfAt u.val (frozenIndex p n j),Fin.elim0) ∈ A := by
    intro u
    have h := hWA (u.val.1 ∘ (activeFrozenShuffle p n).symm,u.val.2) u.property
    have he : (fun j => vfAt u.val (frozenIndex p n j)) =
        (u.val.1 ∘ (activeFrozenShuffle p n).symm) ∘ Fin.castAdd n := by
      funext j
      change u.val.1 (frozenIndex p n j) = u.val.1 ((activeFrozenShuffle p n).symm (Fin.castAdd n j))
      rw [activeFrozenShuffle_symm_prefix]
    exact (congrArg (fun f : Fin p → VF (M := M) => (f,Fin.elim0)) he).symm ▸ h
  let g := gammaPartialFamilyLiftIso (Set.subset_univ _) hD A T hT hXA
  refine ⟨⟨l,partialContractionSchema T hT,
    fun x => partialContractionSchema_finite hκ hs hr T hT hDfin x.val.1,
    e.trans (gammaLogicInput B) g,?_⟩⟩
  intro u j
  change vfAt (g.equiv (e.equiv u)).val (Fin.castAdd n j) = _
  rw [gammaPartialFamilyLiftIso_frozen]
  change vfAt (e.equiv u).val (frozenIndex p n j) = _
  rw [gammaVFCoordinateIso_value]
  change u.val.1 (activeFrozenShuffle p n (frozenIndex p n j)) = u.val.1 (Fin.castAdd n j)
  rw [activeFrozenShuffle_frozen]

end IntegrationInACVF.Section6
