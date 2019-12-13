import sieve
import sites
import category_theory.limits.shapes.equalizers
import category_theory.const

namespace category_theory
namespace category_theory.limits
namespace category_theory.functor

section sheaves
universes w v u
open opposite

variables {C : Type u} [CCat : category.{v} C] 
variables {D : Type w} [DCat : category.{max u v} D]
variables [products : limits.has_products.{max u v} D]
include CCat products

def restriction_map (F : Cᵒᵖ ⥤ D) {U : C} (S : @sieve.{v} C CCat U) : 
    F.obj (op U) ⟶ ∏ (λ k : sieve_domain S, F.obj (op k.Y)) := 
    limits.pi.lift (λ k : sieve_domain S, F.map k.f.op) 

include DCat

structure separated_presheaf (J : @grothendieck_topology C CCat) :=
(F : Cᵒᵖ ⥤ D)
(identity : ∀ {U : C} (S : sieve.{v} U) (S ∈ J.coverings U), 
    mono (restriction_map F S))

omit CCat products
end sheaves

open opposite

universes u v

variables {C : Type u} [𝒞 : category.{v} C]
variables {D : Type u} [Dc : category.{max u v} D]
variables (F : Cᵒᵖ ⥤ D) {J : @grothendieck_topology C 𝒞}
include 𝒞

/- Now we define the notion of a sheaf from a category with a grothendieck topology
Want to define it as an equalizer of a certain sequence

TODO:
1. define objects of the sequence.
2. get the "natural" maps induced by universal properties + functor
3. define sheaf :)
-/

structure domain (X : C) (S : sieve.{v} X) :=
(Y : C)
(f : Y ⟶ X)
(in_cover : f ∈ S.map Y)

set_option pp.universes true

/- Defining maps which "chooses" elements of C that are in the products which are in the "sheaf" sequence -/
def fan_prod (X : C) (S : sieve.{v} X) := λ k : domain X S, F.obj (op k.Y)

def fan_prod_pullback (X : C) (S : sieve.{v} X) [limits.has_pullbacks.{v} C] := λ k : domain X S × domain X S, F.obj (op (limits.pullback k.1.f k.2.f))

variable [products : limits.has_products.{max u v} D]
include Dc products
/- Defining elements of the "sheaf" sequence -/
def id_prod (X : C) (S : sieve.{v} X) := ∏ (fan_prod F X S)

def gluing_prod (X : C) (S : sieve.{v} X) [limits.has_pullbacks.{v} C] := ∏ (fan_prod_pullback F X S)

/- Defining maps of the sequence-/
def cover_proj (X : C) (S : sieve.{v} X) : F.obj (op X) ⟶ (∏ (fan_prod F X S)) := limits.pi.lift (λ k : domain X S, F.map k.f.op)

def proj_map_1' (X : C) (S : sieve.{v} X) [limits.has_pullbacks.{v} C] : Π k : domain X S × domain X S, ∏ (fan_prod F X S) ⟶ (fan_prod_pullback F X S) k := 
λ k : domain X S × domain X S, (limits.pi.π (fan_prod F X S) k.1) ≫ F.map (limits.pullback.fst.op)

def proj_map_1 (X : C) (S : sieve.{v} X) [limits.has_pullbacks.{v} C] : ∏ (fan_prod F X S) ⟶ ∏ (fan_prod_pullback F X S) := limits.pi.lift (proj_map_1' F X S)

def proj_map_2' (X : C) (S : sieve.{v} X) [limits.has_pullbacks.{v} C] : Π k : domain X S × domain X S, ∏ (fan_prod F X S) ⟶ (fan_prod_pullback F X S) k := 
λ k : domain X S × domain X S, (limits.pi.π (fan_prod F X S) k.2) ≫ F.map (limits.pullback.snd.op)

def proj_map_2 (X : C) (S : sieve.{v} X) [limits.has_pullbacks.{v} C] : ∏ (fan_prod F X S) ⟶ ∏ (fan_prod_pullback F X S) := limits.pi.lift (proj_map_2' F X S)

class sheaf (F : Cᵒᵖ ⥤ D) [limits.has_pullbacks.{v} C] :=
(commuting : ∀ (X : C) (S ∈ J.coverings X), (cover_proj F X S) ≫ (proj_map_1 F X S) = (cover_proj F X S) ≫ (proj_map_2 F X S))
(limit : ∀ (X : C) (S : sieve.{v} X) (covering : S ∈ J.coverings X), 
limits.is_limit (limits.fork.of_ι (cover_proj F X S) (commuting X S covering)))

end category_theory.functor
end category_theory.limits
end category_theory