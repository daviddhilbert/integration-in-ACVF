module

public import IntegrationSection6.GammaSchemaNativeRows
public import IntegrationSection6.GammaSchemaIndexedObjects
public import IntegrationSection6.GammaSortedParameterPreservation

@[expose] public section

/-! The sorted total-row code is the literal indexed RV carrier.
Transporting equal carrier presentations preserves every RV index label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}

theorem indexed_rv_raw_row_code
    {T : Set (Fin p → RV (M := M))}
    {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
    (BP : GammaFiniteGraphPresentation B p d T R)
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv))
    (w : Fin (p+a) → RV (M := M)) :
    rvValues w ∈ rawRowTotal (gammaRawObjectDomain BP.toGamma.toGammaRVObject) F.domain ↔
      w ∈ indexedDomain T (fun t => F.rowDomain (rvValues t)) := by
  have hFirst : rvValues (indexedLeft w) ∈ gammaRawObjectDomain BP.toGamma.toGammaRVObject ↔
      indexedLeft w ∈ T :=
    (gammaRawObjectDomain_tuple_iff BP.toGamma.toGammaRVObject (indexedLeft w)).trans
      (Set.ext_iff.mp BP.domain_eq (indexedLeft w))
  have hSecond : rvValues w ∈ F.domain ↔ indexedRight w ∈ F.rowDomain (rvValues (indexedLeft w)) := by
    change rvValues w ∈ F.domain ↔
      Fin.append (rvValues w ∘ Fin.castAdd a) (rvValues w ∘ Fin.natAdd p) ∈ F.domain
    exact Iff.of_eq (congrArg (fun z : Fin (p+a) → M => z ∈ F.domain)
      (Fin.append_castAdd_natAdd (f := rvValues w)).symm)
  exact and_congr hFirst hSecond

theorem gamma_rv_label_prefix_congr
    {A A' : Set (Point (M := M) 0 (p+a))}
    {D D' : Set (Point (M := M) 0 (p+b))}
    (e : GammaIso B A D)
    (hPrefix : ∀ q, (e.equiv q).val.2 ∘ Fin.castAdd b = q.val.2 ∘ Fin.castAdd a)
    (hA : A=A') (hD : D=D') :
    ∀ q, ((e.congr hA hD).equiv q).val.2 ∘ Fin.castAdd b = q.val.2 ∘ Fin.castAdd a := by
  intro q
  rw [gammaIsoCongr_value]
  exact hPrefix _

end IntegrationInACVF.Section7
