module

public import Integration7.GammaVolumeRelabelGeometry
public import Integration7.GammaVolumeSliceAssemblyGeometry

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! An original-Gamma label equivalence preserving the entire volume tuple
and a retained density realizes a genuine Gamma volume isomorphism. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7
open SpecialTransformations.Section5 (Point GammaRVFiniteObject rvObjectDomain rvObjectArity GammaGraphDefinable)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

theorem gamma_coordinate_density_equivalence_realize
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : GammaRVFiniteObject B (k+1))
    (hUC : U.codes ⊆ (C.base : Set M)) (hVC : V.codes ⊆ (C.base : Set M))
    (δ : Fin (rvObjectArity U.object)) (ε : Fin (rvObjectArity V.object))
    (hδ : ∀ u : rvObjectDomain U.object, (u.val δ).val ≠ iRVZero)
    (hε : ∀ v : rvObjectDomain V.object, (v.val ε).val ≠ iRVZero)
    (e : GammaRVIso U.toGammaRVObject V.toGammaRVObject)
    (hcoord : ∀ u, gammaVolumeValue V.toGammaRVObject (e.equiv u) = gammaVolumeValue U.toGammaRVObject u)
    (hDensity : ∀ u, (e.equiv u).val ε = u.val δ) :
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
    ∃ f : RVVolumeIso (M := M) (S := (D.base : Set M)) (k := k)
      ((gammaCoordinateDensityObject (M := M) (B := B) (e := k) (k := 0) hc C U hUC δ hδ).extend hCD)
      ((gammaCoordinateDensityObject (M := M) (B := B) (e := k) (k := 0) hc C V hVC ε hε).extend hCD), f.GammaDefinable B := by
  let A := gammaCoordinateDensityObject (M := M) (B := B) (e := k) (k := 0) hc C U hUC δ hδ
  let D := gammaCoordinateDensityObject (M := M) (B := B) (e := k) (k := 0) hc C V hVC ε hε
  let f : A.underlying.obj.domain ≃ D.underlying.obj.domain := {
    toFun := fun u => ⟨(e.equiv ⟨u.val,u.property⟩).val,(e.equiv ⟨u.val,u.property⟩).property⟩
    invFun := fun v => ⟨(e.equiv.symm ⟨v.val,v.property⟩).val,(e.equiv.symm ⟨v.val,v.property⟩).property⟩
    left_inv := fun u => Subtype.ext (congrArg Subtype.val (e.equiv.left_inv ⟨u.val,u.property⟩))
    right_inv := fun v => Subtype.ext (congrArg Subtype.val (e.equiv.right_inv ⟨v.val,v.property⟩)) }
  have hΓ : GammaGraphDefinable B (fun (x : Point (M := M) 0 A.underlying.obj.arity)
      (y : Point (M := M) 0 D.underlying.obj.arity) =>
      ∃ u : A.underlying.obj.domain, u.val = x.2 ∧ (f u).val = y.2) := by
    apply GammaGraphDefinable.congr e.graph
    intro p q
    constructor
    · rintro ⟨u,hu,hq⟩
      exact ⟨⟨u.val,u.property⟩,hu,hq⟩
    · rintro ⟨u,hu,hq⟩
      exact ⟨⟨u.val,u.property⟩,hu,hq⟩
  exact gammaVolumeRelabelRealizeWithGraph hc C f hΓ
    (fun u => hcoord ⟨u.val,u.property⟩) (fun u => hDensity ⟨u.val,u.property⟩)
    (U.real_contains.trans hUC) (gamma_coordinate_density_object_graphs hc C U hUC δ hδ)

end IntegrationInACVF.Section7
