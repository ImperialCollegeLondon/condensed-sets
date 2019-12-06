import topology.compact_open
import topology.stone_cech

/-!
# Extremally disconnected spaces
-/

universe variables u v w

section
variables {X : Type u} {Y : Type v} {Z : Type w}
variables [topological_space Y] [topological_space Z] [t2_space Z]
variables {f : X → Y}

lemma dense_range.equalizer (hfd : dense_range f)
  {g h : Y → Z} (hg : continuous g) (hh : continuous h) (H : g ∘ f = h ∘ f) :
  g = h :=
funext $ λ y, hfd.induction_on y (is_closed_eq hg hh) $ congr_fun H

end

variables (X : Type u) [topological_space X]

open function

/-- An extremally disconnected topological space is a space
in which the closure of every open set is open.
Such spaces are also called Stonean spaces.
The are the projective objects in the category of compact Hausdorff spaces:
this fact is proven in `TODO`. -/
class extremally_disconnected : Prop :=
(open_closure : ∀ U : set X, is_open U → is_open (closure U))

section

include X
def compact_t2.projective : Prop :=
  Π {Y Z : Type u} [topological_space Y] [topological_space Z],
  by exactI Π [compact_space Y] [t2_space Y] [compact_space Z] [t2_space Z],
  by exactI Π {f : X → Z} {g : Y → Z} (hf : continuous f) (hg : continuous g) (g_sur : surjective g),
  ∃ h : X → Y, continuous h ∧ g ∘ h = f

end

variable {X}

lemma stone_cech.projective [discrete_topology X] : compact_t2.projective (stone_cech X) :=
begin
  introsI Y Z _tsY _tsZ _csY _t2Y _csZ _csZ f g hf hg g_sur,
  let s : Z → Y := λ z, classical.some $ g_sur z,
  have hs : g ∘ s = id := funext (λ z, classical.some_spec (g_sur z)),
  let t := s ∘ f ∘ stone_cech_unit,
  have ht : continuous t := continuous_of_discrete_topology,
  let h : stone_cech X → Y := stone_cech_extend ht,
  have hh : continuous h := continuous_stone_cech_extend ht,
  use [h, hh],
  have H : dense_range (stone_cech_unit : X → stone_cech X),
  { rw dense_range_iff_closure_range, exact stone_cech_unit_dense },
  apply H.equalizer (hg.comp hh) hf,
  rw [comp.assoc, stone_cech_extend_extends ht, ← comp.assoc, hs, comp.left_id],
end

