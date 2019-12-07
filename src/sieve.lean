import category_theory.opposites
import category_theory.hom_functor
import category_theory.limits.shapes.products
import category_theory.limits.shapes.pullbacks
import topology.opens
import topology.category.Top.opens

namespace category_theory
namespace category_theory.limits
namespace category_theory.functor

open opposite

universes v u

section
variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

 /- Maybe define sieve as a subfunctor? (but then I have to define subfunctor...)
 
 structure subfunctor (F : C ⥤ D) :=
(G : C ⥤ D)
(obj : ∀ (c : C), ) -/

/- Could potentially simplify hom definition by using hom_obj in hom_functor.lean somehow...-/
structure sieve (X : C) := 
(map : Π (Y : C), set (Y ⟶ X))
(comp : ∀ (Y Z: C) (g : Y ⟶ Z) (f ∈ map Z), g ≫ f ∈ map Y)

def id_sieve (X : C) : sieve.{v} X := ⟨λ (Y : C), {f | true}, by tidy⟩

def pullback_sieve {X Y : C} (f : Y ⟶ X) (S : sieve.{v} X) : sieve.{v} Y 
    := ⟨λ Z, {g | g ≫ f ∈ S.map Z}, by {tidy, apply S.comp, exact H}⟩

lemma pullback_id_sieve {X Y : C} (f : Y ⟶ X) 
    : pullback_sieve f (id_sieve X) = id_sieve Y := by tidy

omit 𝒞
end

structure grothendieck_topology (C : Type u) [category.{v} C] :=
(coverings : Π (X : C), set (sieve.{v} X))
(base_change : ∀ (X Y : C) (S : sieve.{v} X) (f : Y ⟶ X), 
    S ∈ coverings X → (pullback_sieve f S) ∈ coverings Y)
(local_character : ∀ (X : C) (S T : sieve.{v} X) (_ : S ∈ coverings X), 
    (∀ (Y : C) (f : Y ⟶ X) (_ : f ∈ S.map Y), 
         (pullback_sieve f T) ∈ coverings Y) → T ∈ coverings X)
(id : ∀ (X : C), id_sieve X ∈ coverings X)


open topological_space

-- this is quite bad, especially base_change 
-- I find it annoying to switch between set theory 
-- and the category of open sets... there's some of ulift, plift magic
-- there should definitely be an easy way of doing this 
-- (tidy doesn't work / produces something with I don't understand)
def grothendieck_topology_of_topology (M : Top.{u}): 
    grothendieck_topology (opens M) := 
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
        set s : sieve.{u} X := id_sieve X with sdef,
        have h1 : 𝟙 X ∈ s.map X := by tidy,
        rw h at h1,
        rw set.mem_empty_eq at h1,
        exact h1,
    }⟩

end category_theory.functor
end category_theory.limits
end category_theory