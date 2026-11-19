import Integration7.GammaNamedAllDegreeClasses
import Integration7.HKVolumeBlowupSemiring
import Integration7.GammaRVScalarMapGraphs
import Integration7.GammaRVMapInverseGraphs
import Integration7.GammaActualRVProducts
import IntegrationSection6.GammaRVProductRelations

/-! Gamma graphs of actual products of corrected all-degree RV volume
objects. A uniform Gamma predicate on all-degree objects (Gamma domain,
coordinate map and density) agrees with the degree-zero and positive
Gamma predicates; products of Gamma objects are Gamma. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {S : Set M} {a d : ℕ}

theorem rvUnpack_fst_val (A : DefSet (rawRVSpace (M := M) a) S) (D : DefSet (rawRVSpace (M := M) d) S)
    (w : rvProductDomain A D) : (rvUnpack A D w).val.1 = fun j => w.val (Fin.castAdd d j) := by
  have h := congrArg Subtype.val (rvPack_unpack A D w)
  funext j
  rw [← h]
  exact (Fin.append_left _ _ j).symm

theorem rvUnpack_snd_val (A : DefSet (rawRVSpace (M := M) a) S) (D : DefSet (rawRVSpace (M := M) d) S)
    (w : rvProductDomain A D) : (rvUnpack A D w).val.2 = fun j => w.val (Fin.natAdd a j) := by
  have h := congrArg Subtype.val (rvPack_unpack A D w)
  funext j
  rw [← h]
  exact (Fin.append_right _ _ j).symm

theorem gamma_rv_unpack_fst (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawRVSpace (M := M) a) S) (D : DefSet (rawRVSpace (M := M) d) S)
    (hW : GammaSetDefinable B {p : Point (M := M) 0 (a+d) | p.2 ∈ (rvProductDomain A D).carrier}) :
    RVMapGamma ((Map.prodFst A D).comp (rvUnpack A D)) B :=
  gamma_real_rv_map_graph hc B _ (rvCoordinateSelectMap B.real (Fin.castAdd d)) hW
    (fun w => rvUnpack_fst_val A D w)

theorem gamma_rv_unpack_snd (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawRVSpace (M := M) a) S) (D : DefSet (rawRVSpace (M := M) d) S)
    (hW : GammaSetDefinable B {p : Point (M := M) 0 (a+d) | p.2 ∈ (rvProductDomain A D).carrier}) :
    RVMapGamma ((Map.prodSnd A D).comp (rvUnpack A D)) B :=
  gamma_real_rv_map_graph hc B _ (rvCoordinateSelectMap B.real (Fin.natAdd a)) hW
    (fun w => rvUnpack_snd_val A D w)

/-- A map on a product domain acting factorwise by Gamma maps has a Gamma graph. -/
theorem gamma_rv_product_map {b c : ℕ}
    {A : DefSet (rawRVSpace (M := M) a) S} {D : DefSet (rawRVSpace (M := M) d) S}
    {A' : DefSet (rawRVSpace (M := M) b) S} {D' : DefSet (rawRVSpace (M := M) c) S}
    {f : Map A A'} {g : Map D D'} (hf : RVMapGamma f B) (hg : RVMapGamma g B)
    {E : DefSet (rawRVSpace (M := M) (b+c)) S} (F : Map (rvProductDomain A D) E)
    (hF : ∀ w, (F w).val = Fin.append (f (Map.prodFst A D (rvUnpack A D w))).val
      (g (Map.prodSnd A D (rvUnpack A D w))).val) :
    RVMapGamma F B := by
  apply GammaGraphDefinable.congr (gamma_rv_relation_product hf hg)
  intro p q
  constructor
  · rintro ⟨⟨u,hu,hfu⟩,⟨v,hv,hgv⟩⟩
    have hmem : p.2 ∈ (rvProductDomain A D).carrier := by
      have : p.2 = (rvPackPair A D u v).val := by
        change p.2 = Fin.append u.val v.val
        rw [hu,hv]
        exact Fin.append_castAdd_natAdd.symm
      rw [this]
      exact (rvPackPair A D u v).property
    let w : rvProductDomain A D := ⟨p.2,hmem⟩
    have hwu : Map.prodFst A D (rvUnpack A D w) = u := Subtype.ext ((rvUnpack_fst_val A D w).trans hu.symm)
    have hwv : Map.prodSnd A D (rvUnpack A D w) = v := Subtype.ext ((rvUnpack_snd_val A D w).trans hv.symm)
    refine ⟨w,rfl,?_⟩
    rw [hF w,hwu,hwv,hfu,hgv]
    exact Fin.append_castAdd_natAdd
  · rintro ⟨w,hw,hq⟩
    rw [hF w] at hq
    refine ⟨⟨Map.prodFst A D (rvUnpack A D w),(rvUnpack_fst_val A D w).trans (by rw [hw]),?_⟩,
      ⟨Map.prodSnd A D (rvUnpack A D w),(rvUnpack_snd_val A D w).trans (by rw [hw]),?_⟩⟩
    · funext j
      rw [← hq]
      exact (Fin.append_left _ _ j).symm
    · funext j
      rw [← hq]
      exact (Fin.append_right _ _ j).symm

theorem gamma_rv_product_domain_of
    {A : DefSet (rawRVSpace (M := M) a) S} {D : DefSet (rawRVSpace (M := M) d) S}
    (hA : GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ A.carrier})
    (hD : GammaSetDefinable B {p : Point (M := M) 0 d | p.2 ∈ D.carrier}) :
    GammaSetDefinable B {p : Point (M := M) 0 (a+d) | p.2 ∈ (rvProductDomain A D).carrier} :=
  gamma_actual_rv_product_domain A D hA hD

/-- A map to `RV^0` on a Gamma domain has a Gamma graph. -/
theorem RVMapGamma.of_arity_zero {A : DefSet (rawRVSpace (M := M) a) S}
    {D : DefSet (rawRVSpace (M := M) 0) S} (f : Map A D)
    (hA : GammaSetDefinable B {p : Point (M := M) 0 a | p.2 ∈ A.carrier}) : RVMapGamma f B := by
  have h := (gammaLogicInput B).restrict_graph hA (gamma_global_map_graph (B := B)
    (mixedCoordinatePointMap (Fin.elim0 : Fin 0 → Fin 0) (Fin.elim0 : Fin 0 → Fin a) B.real))
  apply GammaGraphDefinable.congr h
  intro p q
  constructor
  · rintro ⟨hp,-⟩
    refine ⟨⟨p.2,hp⟩,rfl,?_⟩
    funext i
    exact Fin.elim0 i
  · rintro ⟨u,hu,-⟩
    refine ⟨show p.2 ∈ A.carrier by rw [← hu]; exact u.property,?_⟩
    refine Prod.ext (funext (fun i => Fin.elim0 i)) (funext (fun i => Fin.elim0 i))

end IntegrationInACVF.Section7

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {S : Set M}

/-- Uniform Gamma predicate on corrected all-degree RV volume objects. -/
structure RVVolumeObject.Gamma (n : ℕ) (U : RVVolumeObject (M := M) S n) (B : Base (M := M)) : Prop where
  domain : GammaSetDefinable B {p : Point (M := M) 0 (underlying S n U).obj.arity |
    p.2 ∈ (underlying S n U).obj.domain.carrier}
  coordinates : RVMapGamma (underlying S n U).obj.volume B
  density : RVMapGamma (form S n U).map B

theorem RVVolumeObject.Gamma.ofForm (n : ℕ) (U : RVFiniteObject (M := M) S n) (ω : VolumeForm U.obj.domain)
    (hD : GammaSetDefinable B {p : Point (M := M) 0 U.obj.arity | p.2 ∈ U.obj.domain.carrier})
    (hV : RVMapGamma U.obj.volume B) (hω : RVMapGamma ω.map B) :
    RVVolumeObject.Gamma n (ofForm S n U ω) B := by
  cases n <;> exact ⟨hD,hV,hω⟩

theorem RVVolumeObject.Gamma.zero_iff (U : ZeroRVVolumeObject (M := M) S) :
    RVVolumeObject.Gamma 0 U B ↔ U.Gamma B :=
  ⟨fun h => ⟨h.domain,h.density⟩,
    fun h => ⟨h.domain,RVMapGamma.of_arity_zero _ h.domain,h.density⟩⟩

theorem RVVolumeObject.Gamma.positive_iff {k : ℕ} (U : PositiveRVVolumeObject (M := M) S k) :
    RVVolumeObject.Gamma (k+1) U B ↔ VolumeObjectGamma U B :=
  ⟨fun h => ⟨h.coordinates,h.density⟩,
    fun h => ⟨h.coordinates.domain,h.coordinates,h.density⟩⟩

theorem RVVolumeObject.Gamma.product (hc : CanonicalStructure.IsCanonical (M := M)) {n m : ℕ}
    {U : RVVolumeObject (M := M) S n} {V : RVVolumeObject (M := M) S m}
    (hU : RVVolumeObject.Gamma n U B) (hV : RVVolumeObject.Gamma m V B) :
    RVVolumeObject.Gamma (n+m) (HK.product S n m U V) B := by
  let A := underlying S n U
  let D := underlying S m V
  have hW := gamma_rv_product_domain_of hU.domain hV.domain
  have hfst := gamma_rv_unpack_fst hc A.obj.domain D.obj.domain hW
  have hsnd := gamma_rv_unpack_snd hc A.obj.domain D.obj.domain hW
  apply RVVolumeObject.Gamma.ofForm (n+m) _ _ hW
  · exact (RVMapGamma.append (hfst.comp hU.coordinates) (hsnd.comp hV.coordinates)).congr
      (fun _ => rfl)
  · exact (RVMapGamma.scalarMul hc (hfst.comp hU.density) (hsnd.comp hV.density)).congr
      (fun _ => rfl)

abbrev GammaRVObjects (B : Base (M := M)) (S : Set M) (n : ℕ) :=
  {U : RVVolumeObject (M := M) S n // RVVolumeObject.Gamma n U B}

def GammaRVObjects.product (hc : CanonicalStructure.IsCanonical (M := M)) {n m : ℕ}
    (U : GammaRVObjects B S n) (V : GammaRVObjects B S m) : GammaRVObjects B S (n+m) :=
  ⟨HK.product S n m U.val V.val,RVVolumeObject.Gamma.product hc U.property V.property⟩

end IntegrationInACVF.Section7.HK
