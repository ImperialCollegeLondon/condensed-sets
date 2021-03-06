import category_theory.opposites
import category_theory.limits.shapes.products
import category_theory.limits.shapes.pullbacks
import sieve

namespace category_theory
namespace category_theory.limits

section topologies
universes v u

variables (C : Type u) [category.{v} C]

-- SGA 4 II Def 1.1.
structure grothendieck_topology :=
(coverings : Π (X : C), set (sieve.{v} X))
(base_change : ∀ (X Y : C) (S : sieve.{v} X) (f : Y ⟶ X), 
    S ∈ coverings X → (pullback_sieve f S) ∈ coverings Y)
(local_character : ∀ (X : C) (S T : sieve.{v} X) (_ : S ∈ coverings X), 
    (∀ (Y : C) (f : Y ⟶ X) (_ : f ∈ S.map Y), 
         (pullback_sieve f T) ∈ coverings Y) → T ∈ coverings X)
(id : ∀ (X : C), id_sieve X ∈ coverings X)

--TODO coverings is 'cofiltrant' [SGA 4 II 1.1.1.]

-- how to generate this? @[ext] didn't work for because of the explicit universe parameters
lemma grothendieck_topology_ext {J K : grothendieck_topology C}:
    J.coverings = K.coverings → J = K := by {cases K, intro H, cases J, tidy}

-- SGA 4 II 1.1.2. topologies plus ou moins fine
instance grothendieck_topology_partial_order:
    partial_order (grothendieck_topology C) :=
    {   le := (λ J, λ K, J.coverings ≤ K.coverings),
        le_refl := by {intros J X, exact le_refl (J.coverings X), },
        le_trans := by {intros J K L hJK hKL X, exact le_trans (hJK X) (hKL X),},
        le_antisymm := by {
            intros J K hJK hKJ, 
            apply grothendieck_topology_ext, ext X S,
            split,
            intro hS,
            exact hJK X hS,
            intro hS,
            exact hKJ X hS, }
    }

-- SGA 4 II 1.1.3. intersection topology
instance grothendieck_topology_has_Inf:
    lattice.has_Inf (grothendieck_topology C) :=
    { Inf := λ T : set (grothendieck_topology C), ⟨ λ U : C, 
            ⋂ (J : grothendieck_topology C) (H : J ∈ T), J.coverings U,
        by { tidy, apply H_w.base_change, exact a H_w H_w_1, },
        by { 
            tidy, 
            apply H_w.local_character X S T_1, 
            exact _x H_w H_w_1,
            intros Y f hf,
            exact a Y f hf H_w H_w_1, },
        by {tidy, exact H_w.id X, } ⟩ }

-- SGA 4 II 1.1.4. discrete (top) and chaotic (bot) topologies
instance grothendieck_topology_order_top:
    lattice.order_top (grothendieck_topology C) :=
    { top := ⟨λ U, {a | true}, by tidy, by tidy, by tidy⟩,
      le_top := by tidy,
      ..grothendieck_topology_partial_order C}

instance grothendieck_topology_order_bot:
    lattice.order_bot (grothendieck_topology C) :=
    { bot := ⟨ λ U, {id_sieve U}, 
        by {
            tidy,
            rw a,
            rw pullback_id_sieve,
        }, by {
            tidy,
            have H1 : (𝟙 X) ∈ S.map X,
                rw h,
                tidy,
            have H := a X (𝟙 X) H1,
            rw <- H,
            apply sieve_ext, ext,
            have H : x_1 = x_1 ≫ 𝟙 X := by tidy,
            split, {
                intro hx,
                rw H at hx,
                exact hx,
            }, {
                intro hx,
                have : (x_1 ≫ 𝟙 X) ∈ T.map x := hx,
                rw <- H at this,
                exact this,
            },
        }, by tidy⟩,
    bot_le := by {
        intros J U S hS,
        have H : S = id_sieve U := by tidy,
        rw H,
        exact J.id U,
      },
      ..grothendieck_topology_partial_order C}
end topologies

section topologies
universes v u

--SGA 4 II 1.1.6. topology generated by family of morphisms 
def topology_gen_by {C : Type u} [iC : category.{v} C] (fa : Π X Y : C, set (Y ⟶ X)):
    @grothendieck_topology C iC := lattice.Inf {J | ∀ X Y : C, sieve_gen_by (fa X) ∈ J.coverings X}

def is_fibreproduct {C : Type u} [iC : category.{v} C] 
    {A X Y Z : C} (pX : A ⟶ X) (pY : A ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z) :=
    ∀ B : C, ∀ fx : B ⟶ X, ∀ fy : B ⟶ Y, fx ≫ f = fy ≫ g → 
        (∃ h : B ⟶ A, h ≫ pX = fx ∧ h ≫ pY = fy ∧ 
        (∀ h1 : B ⟶ A, (h1 ≫ pX = fx ∧ h1 ≫ pY = fy) → h1 = h))

def is_squareable {C : Type u} [iC : category.{v} C] {X Y :C} (f : Y ⟶ X) :=
    ∀ Z : C, ∀ g : Z ⟶ X, ∃ A : C, ∃ pX : A ⟶ Z, ∃ pY : A ⟶ Y, 
        is_fibreproduct pX pY g f

--SGA 4 II def 1.3. pretopology
structure pretopology (C : Type u) [iC : category.{v} C] :=
(coverings : Π X : C, set (Π Y : C, set (Y ⟶ X)))
(squareable : ∀ X : C, ∀ fa : (Π Y : C, set (Y ⟶ X)), 
    fa ∈ coverings X → ∀ {Y : C} (f : Y ⟶ X), f ∈ fa Y → is_squareable f)
(basechange : ∀ X : C, ∀ fa : (Π Z : C, set (Z ⟶ X)), ∀ {Y : C} (f : Y ⟶ X),
    fa ∈ coverings X → (λ Z : C, {g : Z ⟶ Y | ∃ Xa : C, ∃ h : Xa ⟶ X, 
        h ∈ fa Xa ∧ ∃ p : Z ⟶ Xa, is_fibreproduct p g h f}) ∈ coverings Y)
(local_character : sorry)
(identity : ∀ X : C, sorry)

--TODO prove Prop 1.4

end topologies

section sites
universes v u

variables (cat : Type u) [icat : category.{v} cat]
include icat

-- SGA 4 II 1.1.5
structure site := 
(top : @grothendieck_topology cat icat)

variable C : site cat

def covering_morphisms (X : cat) (fa : Π Y : cat, set (Y ⟶ X)) :=
    sieve_gen_by fa ∈ C.top.coverings X
end sites

section sites
universe v
open topological_space

-- this is quite bad, especially base_change 
-- I find it annoying to switch between set theory 
-- and the category of open sets... there's some of ulift, plift magic
-- there should definitely be an easy way of doing this 
-- (tidy doesn't work / produces something with I don't understand)

-- maybe it can be simplified by defining it as the topology generated by open covers.
def grothendieck_topology_of_topology (M : Top.{v}): 
    @grothendieck_topology (opens M) opens.opens_category := 
    ⟨λ X : opens M, {s | ∀ x : M, x ∈ X → ∃ Y : opens M, s.map Y ≠ ∅ ∧ x ∈ Y }, 
    by { 
        intros X Y s f hs,
        intros x hx,
        have hx' : x ∈ X,
            have H : Y ⊆ X := f.down.down,
            exact H hx,
        have h := hs x hx',
        cases h with Z hZ,
        refine ⟨Z ∩ Y, _, _⟩,
        {   rw set.ne_empty_iff_nonempty,
            rw set.ne_empty_iff_nonempty at hZ,
            cases hZ.1 with i hi,
            have h1 : Z ∩ Y ≤ Y,
            {   intros w hw,
                have h3 : (Z ∩ Y).val = Z.val ∩ Y.val := by tidy,
                rw h3 at hw,
                rw set.mem_inter_iff at hw,
                exact hw.2, },
            let g : Z ∩ Y ⟶ Y := ulift.up (plift.up h1),
            have h2 : Z ∩ Y ≤ Z,
            {   intros w hw,
                have h3 : (Z ∩ Y).val = Z.val ∩ Y.val := by tidy,
                rw h3 at hw,
                rw set.mem_inter_iff at hw,
                exact hw.1, },
            let t : Z ∩ Y ⟶ Z := ulift.up (plift.up h2),
            have H : t ≫ i ∈ s.map (Z ∩ Y), 
                apply s.comp, exact hi,
            have H1 : t ≫ i = g ≫ f := by tidy,
            rw H1 at H,
            have H2 : g ∈ (pullback_sieve f s).map (Z ∩ Y) := H,
            existsi g, exact H,
        }, {
            split,
            exact hZ.2,
            exact hx,
        },
    }, by {
        intros X S T hS H x hx,
        cases hS x hx with Y hY,
        rw set.ne_empty_iff_nonempty at hY,
        cases hY.1 with i hi,
        cases H Y i hi x hY.2 with Z hZ,
        rw set.ne_empty_iff_nonempty at hZ,
        cases hZ.1 with j hj,

        refine ⟨Z, _, hZ.2⟩,
        rw set.ne_empty_iff_nonempty,
        existsi j ≫ i,
        exact hj,
    },
    by { 
        intros X x hx,
        refine ⟨X, _, hx⟩,
        intro h,
        set s : sieve.{v} X := id_sieve X with sdef,
        have h1 : 𝟙 X ∈ s.map X := by tidy,
        rw h at h1,
        rw set.mem_empty_eq at h1,
        exact h1,
    }⟩

end sites

open opposite

universes v u

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

structure covering (U : C) :=
(ι : Type v)
(obj : ι → C)
(hom : Π i, obj i ⟶ U)

set_option pp.universes true

/- redefined this as category + grothendieck topology
structure site :=
(index : C → Type v)
(coverings : Π (U : C), index U → covering.{v} U)
(pullback : ∀ {U V: C} (k : index U) (g : V ⟶ U), ∃ (l : index V), ∀ (j : (coverings V l).ι), 
∃ (i : (coverings U k).ι) (h : ((coverings V l).obj j) ⟶ ((coverings U k).obj i)), 
(coverings V l).hom j ≫ g = h ≫ ((coverings U k).hom i))
-/

variables {D : Type u} [Dc : category.{v} D]
variables [products : limits.has_products.{v} D] [pullbacks : limits.has_pullbacks.{v} C]
variables {F : Cᵒᵖ ⥤ D}
include Dc products pullbacks

def asdf (U : C) (CU : covering.{v} U) (i j : CU.ι) := limits.pullback (CU.hom i) (CU.hom j)

/-def obj1 (U : C) (CU : covering U) := (limits.pullback (CU.hom i) (CU.hom j)) -/

def fan1 (U : C) (CU : covering.{v} U) := λ (k : CU.ι × CU.ι), F.obj (op ( limits.pullback (CU.hom k.1) (CU.hom k.2)))

def intersection_prod (U : C) (CU : covering.{v u} U) := limits.pi_obj.{v u} (@fan1 _ _ _ _ _ _ F U CU)

/- TODO: 
Get maps from product of pullbacks to product of U_i
-/

end category_theory.limits
end category_theory