import sieve

namespace category_theory
namespace category_theory.limits
namespace category_theory.functor

open opposite

universes u v

variables {C : Type u} [𝒞 : category.{v} C]
variables {D : Type u} [Dc : category.{v} D] 
variables [pullbacks : limits.has_pullbacks.{v} C] [products : limits.has_products.{v} D]
include products pullbacks Dc 𝒞

variables {F : Cᵒᵖ ⥤ D} {J : @grothendieck_topology C 𝒞}

/- Now we define the notion of a sheaf from a category with a grothendieck topology
Want to define it as an equalizer of a certain sequence

TODO:
1. define objects of the sequence.
2. get the "natural" maps induced by universal properties + functor
3. define sheaf :)
-/

/- Definition of product of image of cover -/

/- def fan1 (X : C) (S ∈ J.coverings X) := λ (Y : C) (s ∈ S Y), (F (op Y)) -/

/- def sheaf_id_obj := limits.pi_obj fan1 X S -/

/- Definition of product of image of pairwise pullbacks of (objects of) cover -/

/- Definition of map from image of object to image of pullback-/

/- Definition of induced map -/

/- Definition of sheaf -/