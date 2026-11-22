import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.SetTheory.Ordinal.Exponential

/-!
# Abstract cores of the paper on reflection of degree Ξ

Abstract statements behind three steps of the paper "Iterating reflection along all Σ₁
presentations reaches the next level of reflection".  Ordinals stay ordinals or become a type
with a well-founded order; constructible levels and definability do not appear.

* **Descent (Lemmas 4.15 and 5.1).**  Lemma 4.15 is `not_cls_of_family` of
  `SelfSupporting.lean` (the earlier paper's Lemma 4.1) with `Π_n` sentences as tests; that
  theorem places no condition on the tests, so nothing new is needed.  Lemma 5.1 weakens its
  hypothesis: a smaller point has to be checked only when it lies in the class of the
  predecessor (`not_cls_of_family_rel`).  To apply it, a test is a set `x`
  and `holds x β` means `x ∈ L_β`; at a limit `μ`, reflecting on `Y` in this sense says that `Y`
  is unbounded in `μ`, so `cls` becomes the class `In_{Z,X}` of Section 5.
* **"Limit of" along a set relation (Corollary 4.7).**  `setCls r θ μ a`: `μ` is a limit above
  `θ` and the class of every predecessor of `a` is unbounded below `μ`.  For a well-founded
  relation `r` this holds iff `θ < μ` and `ω ^ (1 + rank a)` divides `μ`
  (`setCls_iff_rank`), so no `γ` is in the class of a node of rank `≥ γ + 1`
  (`not_setCls_of_succ_le_rank`).  With the ordinals as nodes (`limIter`), the `ξ`-th iterate
  of "limit of" over the limits above `θ`, intersected at limit stages, is
  `{μ > θ : ω ^ (1 + ξ) ∣ μ}` (`limIter_iff`).  Facts (O1) and (O2) of the paper are
  `opow_dvd_of_forall_lt` and `opow_succ_dvd_of_unbounded`.
* **Kleene–Brouwer (Theorem 3.1, first half).**  For a prefix-closed set of finite sequences
  whose one-step extensions follow a well-founded relation `r` and cover its predecessors, the
  Kleene–Brouwer ordering (labels compared by a well-founded `lt`) is well-founded, and the
  `r`-rank of the end of a sequence is at most its Kleene–Brouwer rank (`rank_le_rank_kb`).

Not formalised: the constructible hierarchy, `Σ₁` and `Δ₁` definability, the trees of the
paper and the verification that they give the families of the descent lemmas, the passage from
a set relation in `L_γ` to the parameter bound `θ`, Lemma 4.6 for relations that change with the
level, the linearity of the Kleene–Brouwer ordering and the bound by `δ_α`, and Lemma 4.17.
-/

/-! The definitions `Refl` and `cls`, with `cls_iff` and `cls_refl`, are copied unchanged from
`SelfSupporting.lean`, the Lean file of the earlier paper, so that this file checks on its own. -/

namespace Googology.SelfSupporting

universe u v w

variable {Pt : Type u} {N : Type v} {T : Type w} [LT Pt] [WellFoundedLT Pt]

/-- `μ` reflects on `X`: every test true at `μ` is true at some smaller point of `X`. -/
def Refl (holds : T → Pt → Prop) (μ : Pt) (X : Pt → Prop) : Prop :=
  ∀ t, holds t μ → ∃ β, β < μ ∧ X β ∧ holds t β

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

end Classes

end Googology.SelfSupporting

namespace Googology.DegreeReflection

open Ordinal Order Googology.SelfSupporting

/-! ## Descent with a relativised hypothesis (Lemma 5.1) -/

section Descent

variable {Pt : Type u} {N : Type v} {T : Type w} [LT Pt] [WellFoundedLT Pt]
variable (holds : T → Pt → Prop) (pred : Pt → N → N → Prop) (C : N → Pt → Prop)
  (Z : Pt → N → Prop)

/-- **Descent, relativised.**  As `not_mem_class_of_family` of `SelfSupporting.lean`, but a
smaller point `β` satisfying the test has to give `(β, d) ∈ Z` only when `β` is in the class
of `d`. -/
theorem not_mem_class_of_family_rel
    (hC : ∀ a μ, C a μ → ∀ c, pred μ c a → Refl holds μ (C c))
    (hZ : ∀ δ c, Z δ c → ∃ d t, pred δ d c ∧ holds t δ ∧
      ∀ β, β < δ → C d β → holds t β → Z β d) :
    ∀ δ c, Z δ c → ¬ C c δ := by
  intro δ
  refine WellFounded.induction (C := fun δ => ∀ c, Z δ c → ¬ C c δ) wellFounded_lt δ ?_
  intro δ ih c hc hCc
  obtain ⟨d, t, hpred, ht, hdown⟩ := hZ δ c hc
  obtain ⟨β, hβ, hCd, hβt⟩ := hC c δ hCc d hpred t ht
  exact ih β hβ d (hdown β hβ hCd hβt) hCd

variable (ok : Pt → N → Prop)

/-- **Lemma 5.1** (abstract form, for the actual classes).  If every `(δ, c) ∈ Z` has a
predecessor `d` at `δ` and a test true at `δ` such that every smaller point `β` of the class of
`d` satisfying the test has `(β, d) ∈ Z`, then `δ` is not in the class of `c`. -/
theorem not_cls_of_family_rel
    (hZ : ∀ δ c, Z δ c → ∃ d t, pred δ d c ∧ holds t δ ∧
      ∀ β, β < δ → cls holds pred ok β d → holds t β → Z β d)
    {δ : Pt} {c : N} (hc : Z δ c) : ¬ cls holds pred ok δ c :=
  not_mem_class_of_family_rel holds pred (fun a μ => cls holds pred ok μ a) Z
    (fun _ _ h _ hc => cls_refl holds pred ok h hc) hZ δ c hc

end Descent

/-! ## Ordinal arithmetic -/

section Arith

/-- **(O2)**: if multiples of `ω ^ ζ` are unbounded below `μ`, then `ω ^ (ζ + 1)` divides
`μ`. -/
theorem opow_succ_dvd_of_unbounded {ζ μ : Ordinal.{u}}
    (h : ∀ η, η < μ → ∃ β, η < β ∧ β < μ ∧ ω ^ ζ ∣ β) : ω ^ (ζ + 1) ∣ μ := by
  have d0 : ω ^ ζ ≠ 0 := (opow_pos ζ omega0_pos).ne'
  have hdec := div_add_mod μ (ω ^ ζ)
  have hr : μ % ω ^ ζ = 0 := by
    by_contra hr
    have hlt : ω ^ ζ * (μ / ω ^ ζ) < μ := by
      conv_rhs => rw [← hdec]
      exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr)
    obtain ⟨β, hβ1, hβ2, k, rfl⟩ := h _ hlt
    have hk : μ / ω ^ ζ < k := lt_of_mul_lt_mul_left' hβ1
    have : μ < ω ^ ζ * k := by
      calc μ = ω ^ ζ * (μ / ω ^ ζ) + μ % ω ^ ζ := hdec.symm
        _ < ω ^ ζ * (μ / ω ^ ζ) + ω ^ ζ := (add_lt_add_iff_left _).2 (mod_lt _ d0)
        _ = ω ^ ζ * (μ / ω ^ ζ + 1) := by rw [mul_add_one]
        _ ≤ ω ^ ζ * k := mul_le_mul_right (add_one_le_of_lt hk) _
    exact absurd hβ2 (not_lt.2 this.le)
  rw [hr, add_zero] at hdec
  rcases zero_or_succ_or_isSuccLimit (μ / ω ^ ζ) with hq | ⟨s, hs⟩ | hq
  · rw [← hdec, hq, mul_zero]; exact dvd_zero _
  · exfalso
    rw [← hs, succ_eq_add_one, mul_add_one] at hdec
    have hlt : ω ^ ζ * s < μ := by
      rw [← hdec]; exact lt_add_of_pos_right _ (opow_pos ζ omega0_pos)
    obtain ⟨β, hβ1, hβ2, k, rfl⟩ := h _ hlt
    have hk : s < k := lt_of_mul_lt_mul_left' hβ1
    have : μ ≤ ω ^ ζ * k := by
      rw [← hdec, ← mul_add_one]; exact mul_le_mul_right (add_one_le_of_lt hk) _
    exact absurd hβ2 (not_lt.2 this)
  · obtain ⟨q, hq'⟩ := isSuccPrelimit_iff_omega0_dvd.1 hq.isSuccPrelimit
    refine ⟨q, ?_⟩
    rw [← succ_eq_add_one, opow_succ, mul_assoc, ← hq', hdec]

/-- **(O1)**, in the form used: if `ω ^ (ζ + 1)` divides `μ` for every `ζ < l`, then `ω ^ l`
divides `μ`. -/
theorem opow_dvd_of_forall_lt {l μ : Ordinal.{u}} (h : ∀ ζ, ζ < l → ω ^ (ζ + 1) ∣ μ) :
    ω ^ l ∣ μ := by
  have D0 : ω ^ l ≠ 0 := (opow_pos l omega0_pos).ne'
  rw [dvd_iff_mod_eq_zero]
  by_contra hr
  have hlog : log ω (μ % ω ^ l) < l :=
    (lt_opow_iff_log_lt one_lt_omega0 hr).1 (mod_lt _ D0)
  have h1 := h _ hlog
  have h2 : ω ^ (log ω (μ % ω ^ l) + 1) ∣ ω ^ l * (μ / ω ^ l) :=
    dvd_mul_of_dvd_left (opow_dvd_opow _ (add_one_le_of_lt hlog)) _
  have h3 : ω ^ (log ω (μ % ω ^ l) + 1) ∣ μ % ω ^ l :=
    (dvd_add_iff h2).1 (by rwa [div_add_mod])
  have h4 : μ % ω ^ l < ω ^ (log ω (μ % ω ^ l) + 1) := by
    rw [← succ_eq_add_one]; exact lt_opow_succ_log_self one_lt_omega0 _
  exact absurd (le_of_dvd hr h3) (not_le.2 h4)

end Arith

/-! ## Classes of a set relation under "limit of" (Corollary 4.7) -/

section SetRelation

variable {N : Type v} (r : N → N → Prop) (θ : Ordinal.{u})

/-- The classes of the nodes of a relation `r` that does not depend on the level, under the
operation "limit of": `μ` is in the class of `a` iff `μ` is a limit above `θ` and, for every
predecessor `c` of `a`, the class of `c` is unbounded below `μ`.  This is `cls` of
`SelfSupporting` with ordinals as tests, the test `η` holding at `β` when `η < β`. -/
def setCls (μ : Ordinal.{u}) (a : N) : Prop :=
  cls (fun η β : Ordinal.{u} => η < β) (fun _ => r) (fun μ _ => IsSuccLimit μ ∧ θ < μ) μ a

/-- The defining recursion of `setCls`. -/
theorem setCls_iff_unfold (μ : Ordinal.{u}) (a : N) :
    setCls r θ μ a ↔ IsSuccLimit μ ∧ θ < μ ∧
      ∀ c, r c a → ∀ η, η < μ → ∃ β, β < μ ∧ setCls r θ β c ∧ η < β := by
  unfold setCls
  rw [cls_iff]
  simp only [Refl, and_assoc]

variable (rk : N → Ordinal.{u})

/-- The classes of a level-independent relation, for any rank function `rk`: predecessors have
smaller rank, and every ordinal below the rank of `a` is at most the rank of a predecessor. -/
theorem setCls_iff (h1 : ∀ c a, r c a → rk c < rk a)
    (h2 : ∀ a ζ, ζ < rk a → ∃ c, r c a ∧ ζ ≤ rk c) (a : N) (μ : Ordinal.{u}) :
    setCls r θ μ a ↔ θ < μ ∧ ω ^ (1 + rk a) ∣ μ := by
  have wf : WellFounded r :=
    Subrelation.wf (fun {c a} h => h1 c a h) (InvImage.wf rk wellFounded_lt)
  induction a using wf.induction generalizing μ with
  | _ a ih =>
  rw [setCls_iff_unfold]
  constructor
  · rintro ⟨hlim, hθ, hrefl⟩
    refine ⟨hθ, opow_dvd_of_forall_lt fun ζ hζ => ?_⟩
    rcases eq_or_ne ζ 0 with rfl | hζ0
    · rw [zero_add, opow_one]
      exact isSuccPrelimit_iff_omega0_dvd.1 hlim.isSuccPrelimit
    · have h1le : 1 ≤ ζ := one_le_iff_ne_zero.2 hζ0
      have hζ' : ζ - 1 < rk a := by
        rw [← Ordinal.add_sub_cancel_of_le h1le] at hζ
        exact (add_lt_add_iff_left 1).1 hζ
      obtain ⟨c, hc, hle⟩ := h2 a (ζ - 1) hζ'
      have hc' : ω ^ (1 + rk c + 1) ∣ μ := by
        refine opow_succ_dvd_of_unbounded fun η hη => ?_
        obtain ⟨β, hβ, hcl, hηβ⟩ := hrefl c hc η hη
        exact ⟨β, hηβ, hβ, ((ih c hc β).1 hcl).2⟩
      refine dvd_trans (opow_dvd_opow _ ?_) hc'
      rw [← Ordinal.add_sub_cancel_of_le h1le]
      exact add_le_add (add_le_add le_rfl hle) le_rfl
  · rintro ⟨hθ, hdvd⟩
    have hμ0 : μ ≠ 0 := (lt_of_le_of_lt zero_le hθ).ne'
    have hωdvd : ∀ x : Ordinal.{u}, ω ∣ ω ^ (1 + x) := fun x => by
      rw [opow_one_add]; exact dvd_mul_right _ _
    refine ⟨?_, hθ, fun c hc η hη => ?_⟩
    · refine ⟨fun hmin => hμ0 hmin.eq_bot, ?_⟩
      exact isSuccPrelimit_iff_omega0_dvd.2 (dvd_trans (hωdvd _) hdvd)
    have hd0 : ω ^ (1 + rk c) ≠ 0 := (opow_pos _ omega0_pos).ne'
    have hdvd' : ω ^ (1 + rk c + 1) ∣ μ := by
      refine dvd_trans (opow_dvd_opow _ ?_) hdvd
      rw [add_assoc]
      exact add_le_add le_rfl (add_one_le_of_lt (h1 c a hc))
    obtain ⟨q, hq⟩ := hdvd'
    rw [← succ_eq_add_one, opow_succ, mul_assoc] at hq
    have hq0 : q ≠ 0 := by rintro rfl; exact hμ0 (by rw [hq, mul_zero, mul_zero])
    set m := max η θ with hm
    have hmμ : m < μ := max_lt hη hθ
    have hmlt : m < ω ^ (1 + rk c) * (m / ω ^ (1 + rk c) + 1) := by
      rw [mul_add_one]; exact lt_mul_div_add m hd0
    refine ⟨ω ^ (1 + rk c) * (m / ω ^ (1 + rk c) + 1), ?_, ?_, ?_⟩
    · rw [hq]
      refine mul_lt_mul_of_pos_left ?_ (opow_pos _ omega0_pos)
      have hlim : IsSuccLimit (ω * q) := by
        refine ⟨fun hmin => ?_, isSuccPrelimit_iff_omega0_dvd.2 (dvd_mul_right _ _)⟩
        exact mul_ne_zero omega0_ne_zero hq0 hmin.eq_bot
      refine hlim.add_one_lt ?_
      rw [← lt_mul_iff_div_lt hd0, ← hq]; exact hmμ
    · exact (ih c hc _).2 ⟨lt_of_le_of_lt (le_max_right η θ) hmlt, dvd_mul_right _ _⟩
    · exact lt_of_le_of_lt (le_max_left η θ) hmlt

/-- No point `γ` is in the class of a node whose rank is at least `γ + 1`. -/
theorem not_setCls_of_succ_le (h1 : ∀ c a, r c a → rk c < rk a)
    (h2 : ∀ a ζ, ζ < rk a → ∃ c, r c a ∧ ζ ≤ rk c) {a : N} {γ : Ordinal.{u}}
    (hγ : γ + 1 ≤ rk a) : ¬ setCls r θ γ a := by
  intro h
  obtain ⟨hθ, hdvd⟩ := (setCls_iff r θ rk h1 h2 a γ).1 h
  have hle := le_of_dvd (lt_of_le_of_lt zero_le hθ).ne' hdvd
  have : rk a ≤ ω ^ (1 + rk a) :=
    le_trans le_add_self (right_le_opow _ one_lt_omega0)
  exact absurd (lt_of_lt_of_le (lt_add_one γ) (hγ.trans (this.trans hle))) (lt_irrefl γ)

end SetRelation

section Rank

variable {N : Type u} (r : N → N → Prop) [IsWellFounded N r] (θ : Ordinal.{u})

/-- Below the rank of `a`, every ordinal is at most the rank of a predecessor. -/
theorem exists_le_rank_of_lt_rank {a : N} {ζ : Ordinal.{u}}
    (hζ : ζ < IsWellFounded.rank r a) : ∃ c, r c a ∧ ζ ≤ IsWellFounded.rank r c := by
  rw [IsWellFounded.rank_eq, Ordinal.lt_iSup_iff] at hζ
  obtain ⟨⟨c, hc⟩, hζ⟩ := hζ
  exact ⟨c, hc, Order.lt_succ_iff.1 hζ⟩

/-- **Corollary 4.7.**  For a well-founded relation `r` (fixed, not depending on the level), the
class of a node of rank `ξ` under "limit of" consists of the ordinals `μ > θ` divisible by
`ω ^ (1 + ξ)`. -/
theorem setCls_iff_rank (a : N) (μ : Ordinal.{u}) :
    setCls r θ μ a ↔ θ < μ ∧ ω ^ (1 + IsWellFounded.rank r a) ∣ μ :=
  setCls_iff r θ (IsWellFounded.rank r) (fun _ _ h => IsWellFounded.rank_lt_of_rel h)
    (fun _ _ h => exists_le_rank_of_lt_rank r h) a μ

/-- **Corollary 4.7, last sentence.**  No `γ` is in the class of a node of rank at least
`γ + 1`. -/
theorem not_setCls_of_succ_le_rank {a : N} {γ : Ordinal.{u}}
    (hγ : γ + 1 ≤ IsWellFounded.rank r a) : ¬ setCls r θ γ a :=
  not_setCls_of_succ_le r θ (IsWellFounded.rank r) (fun _ _ h => IsWellFounded.rank_lt_of_rel h)
    (fun _ _ h => exists_le_rank_of_lt_rank r h) hγ

end Rank

/-! ## Iterating "limit of" along the ordinals -/

section Iterate

/-- `limIter θ ξ`: `ξ` steps of "limit of" over the limit ordinals above `θ`.  By
`limIter_iff_unfold`, `μ ∈ limIter θ ξ` iff `μ` is a limit above `θ` and `μ` is a limit of
`limIter θ ζ` for every `ζ < ξ`. -/
def limIter (θ ξ μ : Ordinal.{u}) : Prop :=
  setCls (fun a b : Ordinal.{u} => a < b) θ μ ξ

/-- The defining recursion of `limIter`. -/
theorem limIter_iff_unfold (θ ξ μ : Ordinal.{u}) :
    limIter θ ξ μ ↔ IsSuccLimit μ ∧ θ < μ ∧
      ∀ ζ, ζ < ξ → ∀ η, η < μ → ∃ β, β < μ ∧ limIter θ ζ β ∧ η < β :=
  setCls_iff_unfold _ θ μ ξ

/-- The `ξ`-th iterate of "limit of" over the limit ordinals above `θ`, with intersections at
limit stages, is the class of ordinals `μ > θ` divisible by `ω ^ (1 + ξ)`. -/
theorem limIter_iff (θ ξ μ : Ordinal.{u}) :
    limIter θ ξ μ ↔ θ < μ ∧ ω ^ (1 + ξ) ∣ μ :=
  setCls_iff _ θ id (fun _ _ h => h) (fun _ ζ h => ⟨ζ, h, le_rfl⟩) ξ μ

/-- With `θ = 0`: the `ξ`-th iterate over all limit ordinals is `{μ > 0 : ω ^ (1 + ξ) ∣ μ}`. -/
theorem limIter_zero_iff (ξ μ : Ordinal.{u}) :
    limIter 0 ξ μ ↔ μ ≠ 0 ∧ ω ^ (1 + ξ) ∣ μ := by
  rw [limIter_iff, pos_iff_ne_zero]

end Iterate

/-! ## The Kleene–Brouwer ordering of a well-founded tree (Theorem 3.1) -/

section KleeneBrouwer

variable {E : Type u} (lt : E → E → Prop)

/-- `t` is to the left of `u`: at the first place where they differ, the entry of `t` is
`lt`-smaller than the entry of `u`. -/
def LeftOf (t u : List E) : Prop :=
  ∃ p x y v w, u = p ++ x :: v ∧ t = p ++ y :: w ∧ lt y x

/-- The Kleene–Brouwer ordering: `t` comes before `s` if `t` properly extends `s` or `t` is to
the left of `s`. -/
def KB (t s : List E) : Prop :=
  (∃ w, w ≠ [] ∧ t = s ++ w) ∨ LeftOf lt t s

/-- The Kleene–Brouwer ordering restricted to a set `T` of sequences. -/
def KBOn (T : Set (List E)) (t s : List E) : Prop :=
  t ∈ T ∧ s ∈ T ∧ KB lt t s

/-- Being to the left of an extension of `u`: either to the left of `u`, or an extension of `u`
that is to the left of the added part. -/
theorem leftOf_append {t u z : List E} (h : LeftOf lt t (u ++ z)) :
    LeftOf lt t u ∨ ∃ z', t = u ++ z' ∧ LeftOf lt z' z := by
  obtain ⟨p, x, y, v, w, hu, rfl, hxy⟩ := h
  rcases List.append_eq_append_iff.1 hu with ⟨a, rfl, rfl⟩ | ⟨c, rfl, hc⟩
  · exact Or.inr ⟨a ++ y :: w, by simp, a, x, y, v, w, rfl, rfl, hxy⟩
  · cases c with
    | nil =>
      simp only [List.nil_append] at hc
      exact Or.inr ⟨y :: w, by simp, [], x, y, v, w, by simp [hc], by simp, hxy⟩
    | cons x' c =>
      simp only [List.cons_append, List.cons.injEq] at hc
      obtain ⟨rfl, -⟩ := hc
      exact Or.inl ⟨p, _, y, c, w, rfl, rfl, hxy⟩

/-- A sequence to the left of a one-entry sequence starts with a smaller entry. -/
theorem leftOf_singleton {t : List E} {x : E} (h : LeftOf lt t [x]) :
    ∃ y w, t = y :: w ∧ lt y x := by
  obtain ⟨p, x', y, v, w, hu, rfl, hxy⟩ := h
  cases p with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at hu
    obtain ⟨rfl, -⟩ := hu
    exact ⟨y, w, rfl, hxy⟩
  | cons a p => simp at hu

/-- Nothing is to the left of the empty sequence. -/
theorem not_leftOf_nil (t : List E) : ¬ LeftOf lt t [] := by
  rintro ⟨p, x, y, v, w, hu, -, -⟩
  simp at hu

variable (T : Set (List E))

/-- **The Kleene–Brouwer ordering of a well-founded tree is well-founded.**  `T` is closed
under prefixes, the tree (the relation "is a one-step extension of") is well-founded, and
`lt` is well-founded. -/
theorem kbOn_wellFounded (hlt : WellFounded lt)
    (hT : ∀ s w, s ++ w ∈ T → s ∈ T)
    (hwf : WellFounded fun t s : List E => t ∈ T ∧ ∃ x, t = s ++ [x]) :
    WellFounded (KBOn lt T) := by
  have hout : ∀ s, s ∉ T → Acc (KBOn lt T) s := fun s hs =>
    ⟨_, fun t ht => absurd ht.2.1 hs⟩
  -- the main claim, by induction along the tree
  have key : ∀ u, (∀ t, t ∈ T → LeftOf lt t u → Acc (KBOn lt T) t) →
      ∀ z, Acc (KBOn lt T) (u ++ z) := by
    intro u
    induction u using hwf.induction with
    | _ u ih =>
    intro H
    have step1 : ∀ x z, Acc (KBOn lt T) (u ++ [x] ++ z) := by
      intro x
      induction x using hlt.induction with
      | _ x ihx =>
      intro z
      by_cases hux : u ++ [x] ∈ T
      · refine ih (u ++ [x]) ⟨hux, x, rfl⟩ (fun t ht hleft => ?_) z
        rcases leftOf_append lt hleft with h | ⟨z', rfl, hz'⟩
        · exact H t ht h
        · obtain ⟨y, w, rfl, hyx⟩ := leftOf_singleton lt hz'
          have : u ++ y :: w = u ++ [y] ++ w := by simp
          rw [this]
          exact ihx y hyx w
      · exact hout _ fun h => hux (hT _ _ h)
    have hu : Acc (KBOn lt T) u := by
      refine ⟨_, fun t ht => ?_⟩
      obtain ⟨htT, -, hkb⟩ := ht
      rcases hkb with ⟨w, hw, rfl⟩ | h
      · obtain ⟨x, w', rfl⟩ := List.exists_cons_of_ne_nil hw
        have : u ++ x :: w' = u ++ [x] ++ w' := by simp
        rw [this]
        exact step1 x w'
      · exact H t htT h
    intro z
    cases z with
    | nil => simpa using hu
    | cons x z =>
      have : u ++ x :: z = u ++ [x] ++ z := by simp
      rw [this]
      exact step1 x z
  refine ⟨fun s => ?_⟩
  simpa using key [] (fun t _ h => absurd h (not_leftOf_nil lt t)) s

variable {α : Type u} (r : α → α → Prop) [IsWellFounded α r] (f : List E → α)

/-- **Theorem 3.1, abstract part.**  Let `T` be a prefix-closed set of finite sequences (the
histories) and `f s` the end of the history `s`.  Suppose every one-step extension of a history
ends at an `r`-predecessor of its end, and every `r`-predecessor of the end of a history is the
end of some one-step extension.  Then the tree is well-founded, its Kleene–Brouwer ordering is
well-founded, and the rank of the end of a history is at most the rank of the history in the
Kleene–Brouwer ordering. -/
theorem rank_le_rank_kb (hlt : WellFounded lt) (hT : ∀ s w, s ++ w ∈ T → s ∈ T)
    (hstep : ∀ s x, s ++ [x] ∈ T → r (f (s ++ [x])) (f s))
    (hcover : ∀ s c, s ∈ T → r c (f s) → ∃ x, s ++ [x] ∈ T ∧ f (s ++ [x]) = c) :
    ∃ hKB : WellFounded (KBOn lt T),
      ∀ s, s ∈ T → IsWellFounded.rank r (f s) ≤ (hKB.apply s).rank := by
  have hwf : WellFounded fun t s : List E => t ∈ T ∧ ∃ x, t = s ++ [x] := by
    refine Subrelation.wf (fun {t s} h => ?_) (InvImage.wf f (IsWellFounded.wf (r := r)))
    obtain ⟨ht, x, rfl⟩ := h
    exact hstep s x ht
  have hKB := kbOn_wellFounded lt T hlt hT hwf
  refine ⟨hKB, fun s => ?_⟩
  induction s using hwf.induction with
  | _ s ih =>
  intro hs
  rw [IsWellFounded.rank_eq]
  refine Ordinal.iSup_le fun ⟨c, hc⟩ => ?_
  obtain ⟨x, hx, rfl⟩ := hcover s c hs hc
  refine Order.succ_le_of_lt (lt_of_le_of_lt (ih _ ⟨hx, x, rfl⟩ hx) ?_)
  exact Acc.rank_lt_of_rel (hKB.apply s) ⟨hx, hs, Or.inl ⟨[x], by simp, rfl⟩⟩

/-- Every history other than the empty one comes before it. -/
theorem kbOn_nil {t : List E} (ht : t ∈ T) (hne : t ≠ []) (hnil : [] ∈ T) :
    KBOn lt T t [] :=
  ⟨ht, hnil, Or.inl ⟨t, hne, rfl⟩⟩

end KleeneBrouwer

end Googology.DegreeReflection
