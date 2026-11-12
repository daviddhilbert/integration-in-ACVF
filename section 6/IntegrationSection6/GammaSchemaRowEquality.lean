import IntegrationSection6.GammaSortedSchemaRows
import IntegrationSection6.GammaFamilyQuantifiers
import IntegrationSection6.GammaGraphFormulaCongruence
import IntegrationSection6.GammaGraphPresentationIsomorphisms

/-! Equality of rows of two finite RV schemata is first order over the
original base. This compares the actual global domain and volume formulas,
and transfers their graph presentations by the label identity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

theorem gamma_equal_rows_definable {m : ℕ} (sx : Fin m → SortTag)
    {D E : Set (Fin (p+m) → M)}
    (hD : DefinableOverBase B (Fin.append sp sx) D)
    (hE : DefinableOverBase B (Fin.append sp sx) E) :
    DefinableOverBase B sp {z | (∀ j, sortEval (sp j) (z j)) ∧
      ∀ x : Fin m → M, Fin.append z x ∈ D ↔ Fin.append z x ∈ E} := by
  have h := (gamma_family_row_subset_definable sp sx hD hE).inter
    (gamma_family_row_subset_definable sp sx hE hD)
  convert h using 1
  apply Set.ext
  intro z
  constructor
  · rintro ⟨hz,hEq⟩
    exact ⟨⟨hz,fun x hx => (hEq x).mp hx⟩,hz,fun x hx => (hEq x).mpr hx⟩
  · rintro ⟨⟨hz,hDE⟩,_,hED⟩
    exact ⟨hz,fun x => ⟨hDE x,hED x⟩⟩

def GammaFiniteRVSchema.sameRow (F G : GammaFiniteRVSchema B p a k sp) (z : Fin p → M) : Prop :=
  (∀ j, sortEval (sp j) (z j)) ∧
  (∀ x : Fin a → M, Fin.append z x ∈ F.domain ↔ Fin.append z x ∈ G.domain) ∧
  (∀ x : Fin a → M, ∀ y : Fin k → M,
    Fin.append (Fin.append z x) y ∈ F.volume ↔ Fin.append (Fin.append z x) y ∈ G.volume)

theorem GammaFiniteRVSchema.sameRow_definable (F G : GammaFiniteRVSchema B p a k sp) :
    DefinableOverBase B sp {z | F.sameRow G z} := by
  have hD := gamma_equal_rows_definable (fun _ : Fin a => .rv) F.domain_definable G.domain_definable
  let st := Fin.append sp (fun _ : Fin (a+k) => SortTag.rv)
  have hF := F.volume_definable.preimage_real st (Fin.cast (Nat.add_assoc p a k))
  have hG := G.volume_definable.preimage_real st (Fin.cast (Nat.add_assoc p a k))
  have hV := gamma_equal_rows_definable (fun _ : Fin (a+k) => .rv) hF hG
  have h := hD.inter hV
  convert h using 1
  apply Set.ext
  intro z
  have hAssoc (x : Fin a → M) (y : Fin k → M) :
      Fin.append z (Fin.append x y) ∘ Fin.cast (Nat.add_assoc p a k) = Fin.append (Fin.append z x) y :=
    (Fin.append_assoc z x y).symm
  constructor
  · rintro ⟨hz,hd,hv⟩
    refine ⟨⟨hz,hd⟩,hz,?_⟩
    intro r
    let x : Fin a → M := r ∘ Fin.castAdd k
    let y : Fin k → M := r ∘ Fin.natAdd a
    have hr : Fin.append x y = r := Fin.append_castAdd_natAdd
    constructor
    · rintro ⟨hfr,hs⟩
      have he : Fin.append z r ∘ Fin.cast (Nat.add_assoc p a k) = Fin.append (Fin.append z x) y := by
        rw [← hr,hAssoc]
      exact ⟨he.symm ▸ (hv x y).mp (he ▸ hfr),hs⟩
    · rintro ⟨hgr,hs⟩
      have he : Fin.append z r ∘ Fin.cast (Nat.add_assoc p a k) = Fin.append (Fin.append z x) y := by
        rw [← hr,hAssoc]
      exact ⟨he.symm ▸ (hv x y).mpr (he ▸ hgr),hs⟩
  · rintro ⟨⟨hz,hd⟩,_,hv⟩
    refine ⟨hz,hd,?_⟩
    intro x y
    have he := hv (Fin.append x y)
    change ((Fin.append z (Fin.append x y) ∘ Fin.cast (Nat.add_assoc p a k) ∈ F.volume) ∧
      Fin.append z (Fin.append x y) ∈ sortedUniverse st) ↔
      ((Fin.append z (Fin.append x y) ∘ Fin.cast (Nat.add_assoc p a k) ∈ G.volume) ∧
      Fin.append z (Fin.append x y) ∈ sortedUniverse st) at he
    rw [hAssoc] at he
    have hsort (hxy : Fin.append (Fin.append z x) y ∈ F.volume) : Fin.append z (Fin.append x y) ∈ sortedUniverse st := by
      have hp := F.volume_definable.proper _ hxy
      intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa only [st,Fin.append_left] using hz i
      · refine Fin.addCases (fun l => ?_) (fun l => ?_) i
        · simpa only [st,Fin.append_right,Fin.append_left] using hp (Fin.castAdd k (Fin.natAdd p l))
        · simpa only [st,Fin.append_right,Fin.append_right] using hp (Fin.natAdd (p+a) l)
    have hsortG (hxy : Fin.append (Fin.append z x) y ∈ G.volume) : Fin.append z (Fin.append x y) ∈ sortedUniverse st := by
      have hp := G.volume_definable.proper _ hxy
      intro j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa only [st,Fin.append_left] using hz i
      · refine Fin.addCases (fun l => ?_) (fun l => ?_) i
        · simpa only [st,Fin.append_right,Fin.append_left] using hp (Fin.castAdd k (Fin.natAdd p l))
        · simpa only [st,Fin.append_right,Fin.append_right] using hp (Fin.natAdd (p+a) l)
    exact ⟨fun hx => (he.mp ⟨hx,hsort hx⟩).1,fun hy => (he.mpr ⟨hy,hsortG hy⟩).1⟩

theorem GammaFiniteRVSchema.sameRow_domains (F G : GammaFiniteRVSchema B p a k sp)
    {z : Fin p → M} (h : F.sameRow G z) : F.rowDomain z = G.rowDomain z :=
  Set.ext (fun x => h.2.1 (fun j => (x j).val))

theorem GammaFiniteRVSchema.sameRow_volumes (F G : GammaFiniteRVSchema B p a k sp)
    {z : Fin p → M} (h : F.sameRow G z) : F.rowVolume z = G.rowVolume z := by
  funext x y
  exact propext (h.2.2 (fun j => (x j).val) (fun j => (y j).val))

end IntegrationInACVF.Section6
