import Parikh.Counting
import Mathlib.Computability.RegularExpressions
import Mathlib.Computability.DFA

/-! Concrete regular expressions; regularity means Mathlib's finite-state DFA
predicate, not a new project-specific substitute.
-/
open scoped Computability Pointwise

namespace Parikh
variable {T : Type*}

/-- An explicit alphabet order, supplied as finite data for executable realization. -/
structure AlphabetOrder (T : Type*) where
  letters : List T
  nodup : letters.Nodup
  complete : ∀ a : T, a ∈ letters

/-- Ordered blocks, including the empty alphabet (`eq:representative`). -/
def representative (alphabet : AlphabetOrder T) (v : Vector T) : List T :=
  (alphabet.letters.map fun a => List.replicate (v a) a).flatten

def wordExpression (w : List T) : RegularExpression T :=
  w.foldr (fun a rest => .comp (.char a) rest) .epsilon

/-- Base word followed by one starred word per indexed period (`lem:linear-regular`). -/
def componentExpression (alphabet : AlphabetOrder T) (c : Component T) : RegularExpression T :=
  .comp (wordExpression (representative alphabet c.base))
    (c.periods.foldr (fun p rest =>
      .comp (.star (wordExpression (representative alphabet p))) rest) .epsilon)

/-- Empty union is the zero expression (`eq:regular-construction`). -/
def witnessExpression (alphabet : AlphabetOrder T) (W : Witness T) : RegularExpression T :=
  W.foldr (fun c rest => .plus (componentExpression alphabet c) rest) .zero

/-- Representative words have exactly the prescribed counts (`eq:representative`). -/
theorem representative_counts [DecidableEq T] (alphabet : AlphabetOrder T) (v : Vector T) :
    counts (representative alphabet v) = v := by
  funext a
  change List.count a ((alphabet.letters.map fun b => List.replicate (v b) b).flatten) = v a
  rw [List.count_flatten, List.map_map]
  have hzero : ∀ b, b ≠ a → b ∈ alphabet.letters →
      (List.count a ∘ fun b => List.replicate (v b) b) b = 0 := by
    intro b hba _
    simp [List.count_replicate, hba]
  rw [List.sum_map_eq_nsmul_single a _ hzero,
    List.count_eq_one_of_mem alphabet.nodup (alphabet.complete a)]
  simp

/-- A literal-word expression accepts exactly that word. -/
theorem wordExpression_matches (w : List T) :
    (wordExpression w).matches' = {w} := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change ({[a]} : Language T) * (wordExpression w).matches' = {a :: w}
    rw [ih]
    change Set.image2 (fun u z : List T => u ++ z) {[a]} {w} = {a :: w}
    exact Set.image2_singleton

/-- Concatenation becomes pointwise addition under the Parikh map. -/
theorem image_mul [DecidableEq T] (L M : Language T) :
    image (L * M) = image L + image M := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨u, hu, z, hz, rfl⟩ := Language.mem_mul.mp hw
    exact Set.mem_add.mpr ⟨counts u, ⟨u, hu, rfl⟩, counts z,
      ⟨z, hz, rfl⟩, (counts_append u z).symm⟩
  · intro hv
    obtain ⟨_, ⟨u, hu, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩ := Set.mem_add.mp hv
    exact ⟨u ++ z, Language.append_mem_mul hu hz, counts_append u z⟩

/-- A starred word realizes exactly the additive closure of its count vector,
including the empty word and zero repetitions. -/
theorem wordExpression_star_image [DecidableEq T] (w : List T) :
    image (wordExpression w).star.matches' =
      (AddSubmonoid.closure ({counts w} : Set (Vector T)) : Set (Vector T)) := by
  have hrep : ∀ n : ℕ, counts (List.replicate n w).flatten = n • counts w := by
    intro n
    induction n with
    | zero => ext a; simp [counts]
    | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, counts_append, ih, succ_nsmul]
      exact add_comm _ _
  rw [RegularExpression.matches'_star, wordExpression_matches]
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨ws, rfl, hws⟩ := Language.mem_kstar.mp hu
    have hlist : ws = List.replicate ws.length w :=
      List.eq_replicate_of_mem (fun z hz => Set.mem_singleton_iff.mp (hws z hz))
    exact AddSubmonoid.mem_closure_singleton.mpr
      ⟨ws.length, by rw [hlist]; simpa only [List.length_replicate] using (hrep _).symm⟩
  · intro hv
    obtain ⟨n, rfl⟩ := AddSubmonoid.mem_closure_singleton.mp hv
    refine ⟨(List.replicate n w).flatten, Language.join_mem_kstar ?_, hrep n⟩
    intro z hz
    exact Set.mem_singleton_iff.mpr (List.eq_of_mem_replicate hz)

/-- The ordered product of starred period words realizes the existing additive
closure of the period values; indexed coefficient semantics are reused unchanged. -/
theorem periodExpressions_image [DecidableEq T] (alphabet : AlphabetOrder T)
    (periods : List (Vector T)) :
    image (periods.foldr (fun p (rest : RegularExpression T) =>
      .comp (.star (wordExpression (representative alphabet p))) rest) .epsilon).matches' =
      (AddSubmonoid.closure (Set.range periods.get) : Set (Vector T)) := by
  induction periods with
  | nil =>
    have hnil : counts ([] : List T) = 0 := by ext a; simp [counts]
    ext v
    simp [image, RegularExpression.matches', Language.one_def,
      AddSubmonoid.closure_empty, hnil]
  | cons p ps ih =>
    have hrange : Set.range (p :: ps).get = {p} ∪ Set.range ps.get := by
      rw [Set.range_list_get, Set.range_list_get]
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff, List.mem_cons]
    rw [hrange, AddSubmonoid.closure_union]
    change image ((wordExpression (representative alphabet p)).star.matches' *
      (ps.foldr (fun q (rest : RegularExpression T) =>
        .comp (.star (wordExpression (representative alphabet q))) rest) .epsilon).matches') = _
    rw [image_mul, wordExpression_star_image, representative_counts, ih]
    ext v
    simp only [Set.mem_add, SetLike.mem_coe, AddSubmonoid.mem_sup]

/-- The component expression has exactly the frozen indexed linear denotation
(`lem:linear-regular`); DFA regularity is a separate obligation. -/
theorem componentExpression_image [DecidableEq T] (alphabet : AlphabetOrder T)
    (c : Component T) :
    image (componentExpression alphabet c).matches' = c.denotation := by
  have hliteral : image (wordExpression (representative alphabet c.base)).matches' =
      {c.base} := by
    rw [wordExpression_matches]
    change counts '' ({representative alphabet c.base} : Set (List T)) = {c.base}
    rw [Set.image_singleton, representative_counts]
  change image ((wordExpression (representative alphabet c.base)).matches' *
    (c.periods.foldr (fun p (rest : RegularExpression T) =>
      .comp (.star (wordExpression (representative alphabet p))) rest) .epsilon).matches') = _
  rw [image_mul, hliteral, periodExpressions_image,
    Component.denotation_eq_vadd_closure]
  ext v
  simp only [Set.mem_add, Set.mem_singleton_iff, Set.mem_vadd_set,
    vadd_eq_add, exists_eq_left]

/-- Exact-image half of `witnessExpression_correct`, proved independently of the
remaining DFA clause (`eq:regular-construction`, `thm:converse`). -/
theorem witnessExpression_image [DecidableEq T] (alphabet : AlphabetOrder T) (W : Witness T) :
    image (witnessExpression alphabet W).matches' = W.denotation := by
  induction W with
  | nil => ext v; simp [witnessExpression, RegularExpression.matches', image,
      Language.zero_def, Witness.denotation]
  | cons c W ih =>
    have hcons : Witness.denotation (c :: W) = c.denotation ∪ Witness.denotation W := by
      ext v
      simp [Witness.denotation]
    have hunion : image ((componentExpression alphabet c).matches' +
        (witnessExpression alphabet W).matches') =
        image (componentExpression alphabet c).matches' ∪
          image (witnessExpression alphabet W).matches' :=
      Set.image_union counts _ _
    change image ((componentExpression alphabet c).matches' +
      (witnessExpression alphabet W).matches') = _
    rw [hunion]
    rw [componentExpression_image, ih, hcons]

/-- The constructed expression realizes the exact witness and is DFA-regular (`thm:converse`). -/
theorem witnessExpression_correct [DecidableEq T] (alphabet : AlphabetOrder T) (W : Witness T) :
    image (witnessExpression alphabet W).matches' = W.denotation ∧
      (witnessExpression alphabet W).matches'.IsRegular := by
  refine ⟨witnessExpression_image alphabet W, ?_⟩
  sorry

/-- Abstract semilinear sets are regular Parikh images (`thm:converse`). -/
theorem converse [Finite T] [DecidableEq T] (X : Set (Vector T)) (hX : IsSemilinearSet X) :
    ∃ R : Language T, R.IsRegular ∧ image R = X := by
  sorry

/-- Regular-language specialization using Mathlib's DFA semantics (`thm:parikh-statement`). -/
theorem regular_image [Finite T] [DecidableEq T] (R : Language T) (hR : R.IsRegular) :
    IsSemilinearSet (image R) := by
  sorry

end Parikh
