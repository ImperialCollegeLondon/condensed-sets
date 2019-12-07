/-

# An equalizer lemma.

In category theory, if f and g are morphisms from X to Y, then
the equalizer of (f,g) is isomorphic to the equalizer of (g,f).

-/

import category_theory.limits.shapes.equalizers
import category_theory.discrete_category

open category_theory
open category_theory.limits

universes v u

variables {C : Type u} [𝒞 : category.{v} C] [has_equalizers.{v} C]
include 𝒞

variables {A B : C} (f g : A ⟶ B)

/- I will assume people know the mathematics of equalizers and limits.

## General category-theory set-up:

The abstract small category with two objects and two morphisms

       left
      ----->   
zero          one
      ----->
      right

is called `walking_parallel_pair` and there is an API which means
that you often don't have to use these names explicitly. Let's just call it J.

Say A and B are two objects of a category 𝒞 which has equalizers.
Say f and g are two morphisms from A to B. The functor from the `walking_parallel_pair`
category `J` to 𝒞 sending `zero` to `A`, `one` to `B`, `left` to `f` and `right` to `g` is
called `parallel_pair f g`. We think of this functor as a diagram in the category:

   f   
  ---> 
A      B
  --->  
   g

A term of type `fork f g` is a cone for this diagram, i.e. an object X and
maps X -> A and X -> B making the triangles involving f and g commute.
Note however that this package of data (the maps and the proofs that the
diagrams commute) packaged up as a natural transformation π from the
constant functor J -> 𝒞 to the `parallel_pair F G` functor (recall that a natural
transformation between two functors J ⥤ C is a morphism in C for each object in J,
and a proof that a diagram commutes for each morphism in J). 

Note that the fork is determined by the map ι : X -> A.

## How to work with the limits. 

The limit data itself (the object and the cone and the proof that the
cone satisfies a universal property) is obtained by type class inference.
User access to the limit data is via an API.

The limit object is `equalizer f g`.

The map from this object to A is `equalizer.ι f g` .

The universal property is given by equalizer.lift
-/


#check category_theory.limits.has_limit
#check category_theory.limits.limit
#check equalizer

--set_option profiler true
def equalizer.symm.hom : equalizer g f ⟶ equalizer f g := 
equalizer.lift _ _ (equalizer.ι g f) (equalizer.condition g f).symm
-- elaboration of equalizer.symm.hom took 935ms


/-
  let s : cone (parallel_pair f g) := fork.of_ι (limit.π (parallel_pair g f) walking_parallel_pair.zero)
    begin 
      convert limit.w (parallel_pair g f) walking_parallel_pair_hom.right,
      convert limit.w (parallel_pair g f) walking_parallel_pair_hom.left,
    end
in (has_limit.is_limit (parallel_pair f g)).lift s
-/
#print equalizer.symm.hom

def equalizer.symm : equalizer f g ≅ equalizer g f := 
{ hom := equalizer.symm.hom g f,
  inv := equalizer.symm.hom f g,
  -- this follows from uniqueness of maps making stuff commute
  hom_inv_id' := begin
    letI haslim : has_limit (parallel_pair f g) := by apply_instance,
    rw (haslim.is_limit.uniq haslim.cone (𝟙 (equalizer f g))),
    { rw haslim.is_limit.uniq haslim.cone (equalizer.symm.hom g f ≫ equalizer.symm.hom f g),
      intro j,
      rw category.assoc,
      let XXX := haslim.is_limit.fac,
      unfold equalizer.symm.hom,
      rw haslim.is_limit.fac,
      let YYY := (has_limit.is_limit (parallel_pair f g)).fac (has_limit.cone (parallel_pair f g)) j,
      convert YYY using 1,
      rw YYY,
      sorry},
    { sorry},
--    apply limit.hom_ext,

  end,
  inv_hom_id' := sorry }

