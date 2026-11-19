import Mathlib.Order.WellFounded

/-!
# Self-supporting families have classes that miss their points

This is the abstract descent lemma (Lemma 4.1) of the paper "The least α⁺-recursively Mahlo
ordinal is the least Π₃-reflecting ordinal".  It generalises "self-supporting sets have empty
classes" from a fixed set of nodes to a family that depends on the point.

## Setting

* `Pt` is the type of points (ordinals in the application), with a well-founded `<`.
* `N` is the type of nodes of a presentation; `pred μ c a` says `c` is a predecessor of `a`
  at the point `μ`.
* `T` is the type of tests (strict `Π₂` sentences with parameters in the application);
  `holds t μ` says the test is true at `μ` (and its parameters are present there).
* `Refl holds μ X`: every test true at `μ` is true at some smaller point of `X`
  (`μ` is `Π₂`-reflecting on `X`).
* `cls holds pred ok μ a` is the Mahlo class of the node `a`, by recursion on the point:
  `μ ∈ C(a)` iff `ok μ a` and `μ` reflects on `C(c)` for every predecessor `c` of `a` at `μ`.
  No well-foundedness of `pred` is used.

## Result

A family `Z` of (point, node) pairs is *self-supporting* through tests `τ` if every
`(δ, s) ∈ Z` has a test `τ δ s` true at `δ` such that at every smaller point `β` where that
test holds, `s` has a predecessor `s'` at `β` with `(β, s') ∈ Z`.

Then (`not_mem_class`) no point below `δ` satisfying `τ δ s` lies in the class of `s`.  Hence
`δ` does not reflect on the class of `s` (`not_refl_class`), and `δ` is not in the class of any
node having `s` as a predecessor at `δ` (`not_mem_class_of_pred`).  In the application `Z` is
"`s` is a correct node at the point `δ`", `τ` is its correctness test, and the parent is the
root of the search tree of Section 6 of the paper.

The proof is an infinite descent on the point: a point of the class satisfying the test would
have to reflect the predecessor's own test onto the predecessor's class, giving a smaller
point of the same kind.

What is **not** formalised here: that the search tree of the paper gives such a family, the
well-foundedness of its root, or any of the paper's arguments about constructible levels.
-/

namespace Googology.SelfSupporting

universe u v w

variable {Pt : Type u} {N : Type v} {T : Type w} [LT Pt] [WellFoundedLT Pt]

/-- `μ` reflects on `X`: every test true at `μ` is true at some smaller point of `X`. -/
def Refl (holds : T → Pt → Prop) (μ : Pt) (X : Pt → Prop) : Prop :=
  ∀ t, holds t μ → ∃ β, β < μ ∧ X β ∧ holds t β

section Abstract

variable (holds : T → Pt → Prop) (pred : Pt → N → N → Prop) (C : N → Pt → Prop)
  (Z : Pt → N → Prop) (τ : Pt → N → T)

/-- **Descent lemma.**  Let `C` be any assignment of classes whose members reflect on the
classes of their predecessors.  If `Z` is self-supporting through the tests `τ`, then no point
below `δ` satisfying the test of `(δ, s) ∈ Z` lies in the class of `s`. -/
theorem not_mem_class
    (hC : ∀ a μ, C a μ → ∀ c, pred μ c a → Refl holds μ (C c))
    (hτ : ∀ δ s, Z δ s → holds (τ δ s) δ)
    (hZ : ∀ δ s, Z δ s → ∀ β, β < δ → holds (τ δ s) β → ∃ s', pred β s' s ∧ Z β s') :
    ∀ δ s, Z δ s → ∀ β, β < δ → holds (τ δ s) β → ¬ C s β := by
  intro δ
  refine WellFounded.induction (C := fun δ => ∀ s, Z δ s → ∀ β, β < δ →
    holds (τ δ s) β → ¬ C s β) wellFounded_lt δ ?_
  intro δ ih s hs β hβ hβτ hCs
  obtain ⟨s', hpred, hZ'⟩ := hZ δ s hs β hβ hβτ
  obtain ⟨β', hβ', hC', hτ'⟩ := hC s β hCs s' hpred (τ β s') (hτ β s' hZ')
  exact ih β hβ s' hZ' β' hβ' hτ' hC'

/-- **Lemma 4.1** (the form used in the paper).  Suppose every `(δ, c) ∈ Z`
has a predecessor `d` of `c` at `δ` and a test true at `δ` such that every smaller point `β`
satisfying the test has `(β, d) ∈ Z`.  Then no `(δ, c) ∈ Z` has `δ` in the class of `c`. -/
theorem not_mem_class_of_family
    (hC : ∀ a μ, C a μ → ∀ c, pred μ c a → Refl holds μ (C c))
    (hZ : ∀ δ c, Z δ c → ∃ d t, pred δ d c ∧ holds t δ ∧ ∀ β, β < δ → holds t β → Z β d) :
    ∀ δ c, Z δ c → ¬ C c δ := by
  intro δ
  refine WellFounded.induction (C := fun δ => ∀ c, Z δ c → ¬ C c δ) wellFounded_lt δ ?_
  intro δ ih c hc hCc
  obtain ⟨d, t, hpred, ht, hdown⟩ := hZ δ c hc
  obtain ⟨β, hβ, hCd, hβt⟩ := hC c δ hCc d hpred t ht
  exact ih β hβ d (hdown β hβ hβt) hCd

/-- A point of a self-supporting family does not reflect on the class of its node. -/
theorem not_refl_class
    (hC : ∀ a μ, C a μ → ∀ c, pred μ c a → Refl holds μ (C c))
    (hτ : ∀ δ s, Z δ s → holds (τ δ s) δ)
    (hZ : ∀ δ s, Z δ s → ∀ β, β < δ → holds (τ δ s) β → ∃ s', pred β s' s ∧ Z β s')
    {δ : Pt} {s : N} (hs : Z δ s) : ¬ Refl holds δ (C s) := by
  intro hR
  obtain ⟨β, hβ, hCβ, hβτ⟩ := hR (τ δ s) (hτ δ s hs)
  exact not_mem_class holds pred C Z τ hC hτ hZ δ s hs β hβ hβτ hCβ

/-- A point of a self-supporting family is not in the class of any node that has the family's
node as a predecessor there. -/
theorem not_mem_class_of_pred
    (hC : ∀ a μ, C a μ → ∀ c, pred μ c a → Refl holds μ (C c))
    (hτ : ∀ δ s, Z δ s → holds (τ δ s) δ)
    (hZ : ∀ δ s, Z δ s → ∀ β, β < δ → holds (τ δ s) β → ∃ s', pred β s' s ∧ Z β s')
    {δ : Pt} {s u : N} (hs : Z δ s) (hsu : pred δ s u) : ¬ C u δ :=
  fun hu => not_refl_class holds pred C Z τ hC hτ hZ hs (hC u δ hu s hsu)

/-- A member of the family with a predecessor in the family at the same point is not in its
own class.  (In the application: a correct node that has a correct child.) -/
theorem not_mem_own_class
    (hC : ∀ a μ, C a μ → ∀ c, pred μ c a → Refl holds μ (C c))
    (hτ : ∀ δ s, Z δ s → holds (τ δ s) δ)
    (hZ : ∀ δ s, Z δ s → ∀ β, β < δ → holds (τ δ s) β → ∃ s', pred β s' s ∧ Z β s')
    {δ : Pt} {s s' : N} (hs' : Z δ s') (hpred : pred δ s' s) : ¬ C s δ :=
  not_mem_class_of_pred holds pred C Z τ hC hτ hZ hs' hpred

end Abstract

section Classes

variable (holds : T → Pt → Prop) (pred : Pt → N → N → Prop) (ok : Pt → N → Prop)

/-- The Mahlo classes of a presentation, by recursion on the point: `μ` is in the class of `a`
iff `ok μ a` (the point is a limit containing the node and the parameters) and `μ` reflects on
the class of every predecessor of `a` at `μ`. -/
def cls : Pt → N → Prop :=
  WellFounded.fix (C := fun _ => N → Prop) wellFounded_lt
    (fun μ IH a => ok μ a ∧
      ∀ c, pred μ c a → ∀ t, holds t μ → ∃ β, ∃ h : β < μ, IH β h c ∧ holds t β)

theorem cls_iff (μ : Pt) (a : N) :
    cls holds pred ok μ a ↔
      ok μ a ∧ ∀ c, pred μ c a → Refl holds μ (fun β => cls holds pred ok β c) := by
  unfold cls
  rw [WellFounded.fix_eq]
  constructor
  · rintro ⟨hok, h⟩
    refine ⟨hok, fun c hc t ht => ?_⟩
    obtain ⟨β, hβ, hcl, hβt⟩ := h c hc t ht
    exact ⟨β, hβ, hcl, hβt⟩
  · rintro ⟨hok, h⟩
    refine ⟨hok, fun c hc t ht => ?_⟩
    obtain ⟨β, hβ, hcl, hβt⟩ := h c hc t ht
    exact ⟨β, hβ, hcl, hβt⟩

/-- Members of a class reflect on the classes of their predecessors. -/
theorem cls_refl {μ : Pt} {a : N} (h : cls holds pred ok μ a) {c : N} (hc : pred μ c a) :
    Refl holds μ (fun β => cls holds pred ok β c) :=
  ((cls_iff holds pred ok μ a).1 h).2 c hc

variable (Z : Pt → N → Prop) (τ : Pt → N → T)

/-- **Abstract form for the actual classes.**  For the actual classes of a presentation: if `Z` is
self-supporting through `τ`, then a point `δ` with `(δ, s) ∈ Z` is not in the class of any
node `u` that has `s` as a predecessor at `δ`. -/
theorem not_cls_of_selfSupporting
    (hτ : ∀ δ s, Z δ s → holds (τ δ s) δ)
    (hZ : ∀ δ s, Z δ s → ∀ β, β < δ → holds (τ δ s) β → ∃ s', pred β s' s ∧ Z β s')
    {δ : Pt} {s u : N} (hs : Z δ s) (hsu : pred δ s u) : ¬ cls holds pred ok δ u :=
  not_mem_class_of_pred holds pred (fun a μ => cls holds pred ok μ a) Z τ
    (fun _ _ h _ hc => cls_refl holds pred ok h hc) hτ hZ hs hsu

/-- **Lemma 4.1 for the actual classes.**  If every `(δ, c) ∈ Z` has a predecessor `d` at `δ`
and a test true at `δ` all of whose smaller points `β` have `(β, d) ∈ Z`, then `δ` is not in
the class of `c` for any `(δ, c) ∈ Z`. -/
theorem not_cls_of_family
    (hZ : ∀ δ c, Z δ c → ∃ d t, pred δ d c ∧ holds t δ ∧ ∀ β, β < δ → holds t β → Z β d)
    {δ : Pt} {c : N} (hc : Z δ c) : ¬ cls holds pred ok δ c :=
  not_mem_class_of_family holds pred (fun a μ => cls holds pred ok μ a) Z
    (fun _ _ h _ hc => cls_refl holds pred ok h hc) hZ δ c hc

/-- If a node of the well-founded part at `δ` belongs to such a family at `δ`, the point `δ`
fails the requirement `AllClasses` below.  This is the passage from Theorem M of the paper to
"`δ` is not α⁺-recursively Mahlo". -/
theorem not_forall_cls_of_family
    (hZ : ∀ δ c, Z δ c → ∃ d t, pred δ d c ∧ holds t δ ∧ ∀ β, β < δ → holds t β → Z β d)
    {δ : Pt} {c : N} (hc : Z δ c) (hacc : Acc (fun x y => pred δ x y) c) :
    ¬ ∀ a, Acc (fun x y => pred δ x y) a → cls holds pred ok δ a :=
  fun h => not_cls_of_family holds pred ok Z hZ hc (h c hacc)

/-- The requirement "the point is in the class of every node in the well-founded part of the
presentation at that point" (the shape of α⁺-recursive Mahloness for one presentation). -/
def AllClasses (μ : Pt) : Prop :=
  ∀ a, Acc (fun c d => pred μ c d) a → cls holds pred ok μ a

/-- If a node `u` of the well-founded part at `δ` has a predecessor `s` with `(δ, s)` in a
self-supporting family, the point `δ` fails the requirement `AllClasses`.  In the application
`u` is the root of the search tree and `s` is one of its children. -/
theorem not_allClasses_of_selfSupporting
    (hτ : ∀ δ s, Z δ s → holds (τ δ s) δ)
    (hZ : ∀ δ s, Z δ s → ∀ β, β < δ → holds (τ δ s) β → ∃ s', pred β s' s ∧ Z β s')
    {δ : Pt} {s u : N} (hs : Z δ s) (hsu : pred δ s u)
    (hu : Acc (fun c d => pred δ c d) u) : ¬ AllClasses holds pred ok δ :=
  fun h => not_cls_of_selfSupporting holds pred ok Z τ hτ hZ hs hsu (h u hu)

end Classes

end Googology.SelfSupporting
