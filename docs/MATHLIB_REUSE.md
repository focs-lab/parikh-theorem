# Audit of the pinned Mathlib

Lean 4.34.1; Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`
(release v4.34.1). The dependency manifest records all eight transitive packages.
The audit searched the actual sources before choosing the interfaces.

| Existing source | Reuse and remaining gap |
| --- | --- |
| `Computability/Language.lean` | Reuse `Language`, `Symbol`, and language algebra. No parallel language datatype. |
| `Computability/ContextFreeGrammar.lean` | Reuse `ContextFreeRule`, `ContextFreeGrammar`, `Produces`, `Derives`, `language`, `Language.IsContextFree`. Rewriting context lemmas already exist. No ordered derivation-tree syntax or complete-tree equivalence was found. The existing tree syntax is now connected by proved frontier expansion and complete-tree equivalence. Reuse `Derives.append_left/right`, `Rewrites.input_output` and `nonterminal_input_mem`; the new `rewrites_append_cases` locates a rewrite in either concatenated part, a missing converse to the context lemmas. |
| `ModelTheory/Arithmetic/Presburger/Semilinear/Defs.lean` | Reuse `IsLinearSet`, `IsSemilinearSet`, finitely generated additive closure, and finite-union lemmas. New witness records only supply explicit indexed bases/periods; their denotation-to-Mathlib bridges are now proved. |
| `Algebra/Group/Submonoid/Finsupp.lean` | Reuse `AddSubmonoid.mem_closure_range_iff_of_fintype` to identify indexed natural sums with additive closure. `Set.finite_range`, finite-set enumeration, and Mathlib finite unions finish both witness directions. |
| `Data/List/Count.lean` and finite-sum infrastructure | Reuse `List.count`, lists, `Fin`, `Finset`, natural scalar multiplication and sums. Plugging uses `List.count_flatten` to reduce terminal counts to child sums. No custom vector arithmetic. |
| `Algebra/BigOperators/Group/List/Basic.lean`, `Algebra/BigOperators/Ring/List.lean` | Reuse `List.sum_map_add` and `List.sum_map_mul_right` for production/count accounting, and core `List.length_flatten`, `List.flatten_eq_nil_iff`, `List.forall_mem_map`, `List.mem_flatMap` for holes and support. These are already available through the pinned imports; no new Mathlib dependency is needed. |
| `Computability/RegularExpressions.lean` | Reuse concrete `RegularExpression` constructors and `matches'`. The source explicitly reports no general equivalence with DFAs/NFAs. This project needs only regularity of the constructed finite unions of `u v₁* … vₖ*`; a full equivalence theorem is unnecessary. |
| `Computability/DFA.lean`, `NFA.lean`, `EpsilonNFA.lean` | Reuse `Language.IsRegular`, `NFA.toDFA_correct` and `εNFA.toNFA_correct` where applicable. The proved finite continuation-language NFA for witness expressions reuses `NFA.toDFA_correct` directly. The converse does not require a grammar. |
| `Data/Nat/Log.lean` | Reuse `Nat.clog` for the document's fixed-width bit bound. |
| `Data/Set/Finite/List.lean` | Reuse `List.finite_length_eq` over a finite subtype for production child lists, with finite images and unions for bounded-tree finiteness. No parallel list-enumeration or generic tree-finiteness theory. |
| `Data/List/Sections.lean` | Reuse executable ordered Cartesian products (`List.sections`) and their exact `Forall₂` membership law for bounded-tree enumeration. No custom product enumerator. |
| `Data/Tree/Basic.lean`, `Data/W/*` | Existing binary trees/W-types do not directly provide ordered variable-arity production nodes, nonterminal holes, local RHS-root matching or grammar semantics. A small raw syntax with a separate validity predicate keeps these meanings explicit. |

The tree-semantics milestone also reuses core `List.filterMap_flatten`,
`List.map_congr_left`, `List.flatMap_singleton'`, and `Relation.ReflTransGen`
induction. Frontier projections are thin tree-specific adapters. Forest induction
stays inside the two validity proofs, with no new forest datatype or rewriting
relation. No finite-nonterminal assumption, grammar normalization, leftmost
restriction, or dependency upgrade is needed.

The plugging milestone keeps the accepted syntax and `plug` operation. Its four
new theorems are tree-specific structural adapters: count/size accounting per
hole, support membership after plugging, and preservation of grammar validity
and root when hole labels match. No equivalent theorem for this production-tree
syntax exists in Mathlib. Ordinary list sums and membership handle the child
forests; no new forest representation, statistic, or instance is introduced.

The insertion milestone reuses core `List.mem_iff_getElem?`,
`List.mem_of_getElem?`, `List.getElem?_eq_some_iff`, and
`Option.bind_eq_some_iff` to connect membership with indexed occurrences.
`List.mem_or_eq_of_mem_set`, `List.map_set`, `List.set_getElem_self`, and
`List.set_eq_take_append_cons_drop` handle a single selected child; existing
list-map/flatten lemmas preserve untouched complete branches and exactly one
hole. There is no existing equivalent for this grammar-specific tree syntax.
Three structural adapters establish unchanged no-hole branches, support versus
subtree occurrences, and the outer one-hole context. The accepted plugging
contract then supplies all insertion statistics; ordinary addition and set
union laws finish the proof. No new syntax, statistic, instance, or dependency
is introduced.

The abstract activation milestone searches the pinned list/set infrastructure
and finds no equivalent to this project-specific support transition predicate.
Three thin adapters prove filtering of already-covered operations, activation
when all roots are present, and appending operations covered by an earlier pass.
They use ordinary set-union membership and `Set.union_eq_left`. First-occurrence
reduction reuses `List.Nodup.filter`, `List.mem_filter`, and `List.mem_toFinset`;
no duplicate-removal datatype or algorithm is introduced. Ordinary `List.dedup`
keeps last occurrences, so using it blindly can break prerequisite order.
Multiplicity accounting reuses `List.flatMap`, `List.replicate`,
`List.mem_flatMap`, `List.eq_of_mem_replicate`, `List.count_eq_one_of_mem`,
`List.count_flatMap`, `List.count_replicate`, and `List.sum_map_eq_nsmul_single`.
These are all available through existing imports; no new dependency, finite-label
assumption, statistics, or instance is introduced. The support proofs remain
independent of grammar syntax.

Sequence accounting reuses `List.map_cons`, `List.sum_cons`, ordinary addition,
and `Set.mem_iUnion` for the indexed union of cycle supports. For a distinct
activation order, `List.sum_toFinset` changes the list's weight sum to a finite-set
sum; `List.mem_toFinset` identifies that set with the selected contexts. No new
sum, support-aggregation definition, or enumeration mechanism is needed.
Mathlib has no equivalent to this project's cycle/insertion predicates. The
four new proved adapters establish cycle-root support, exact sequence accounting,
the equivalence between enabled lists and tree insertion sequences, and the
finite activatable-set realization. They reuse the existing `insertion_enabled`
and `insertion_accounting` contracts. The only new import is the project's
`InsertionSequences` module; there is no additional Mathlib dependency or
finite-nonterminal assumption.

The exact `one_linear` equality reuses `Finset.sum_list_map_count` rather than
introducing a new multiset statistic. `List.count_pos_iff` supplies positivity
for every selected context; `add_nsmul` and `Finset.sum_add_distrib` separate the
first copy from additional copies. The only new project adapter,
`contextComponent.mem_denotation_iff`, relates the frozen indexed-list denotation
to coefficients indexed by context syntax. It uses the existing
`Component.denotation_eq_vadd_closure`,
`AddSubmonoid.mem_closure_range_iff_of_fintype`, `Set.mem_vadd_set`, and
`Finset.sum_coe_sort`. This finite reindexing supports distinct contexts with
equal weights without identifying their required roots or supports. The tree
construction reuses `positive_multiplicities`,
`activationOrder_iff_insertionSequence`, and `InsertionSequence.accounting`.
There is no new import, dependency, instance, or definition.

The active-support proof reuses `Finset.mem_union_right`,
`Finset.mem_biUnion`, `Finset.mem_singleton_self`, `List.mem_cons`,
`List.mem_flatten`, and `List.mem_map`. It unfolds the existing recursion with
Lean's `WellFounded.fix_eq`; this keeps previously published generated
simplification declarations stable. No replacement statistics or active-alphabet
definition is introduced. `Valid.support_active` is the stronger open-tree
adapter needed to derive the complete-tree contract.

For production height, core `List.max_mem` selects a child of maximum height,
and `List.foldl_max_eq_max` connects that maximum to the frozen height definition.
The two tree-specific path adapters reuse `List.mem_map`, `List.mem_flatMap`,
and `List.map_eq_nil_iff`; no generic maximum theory is reproved.
`List.toFinset_card_of_nodup` and `Finset.card_le_card` finish the simple-tree
height bound. These facts are available through the existing imports. The only
new import is the project's `ParseTreePaths` module; no new Mathlib dependency,
instance, or finite-nonterminal assumption is needed.

Bounded-open-tree finiteness reuses `List.finite_length_eq`,
`List.attachWith_map_subtype_val`, `Set.Finite.image`, `Set.Finite.union`,
`Set.Finite.biUnion`, and `Set.Finite.subset`. Each production's RHS-root equality
fixes the child-list length. `List.mem_flatMap` passes the active-hole restriction
to children; `List.le_max_of_mem` and `List.foldl_max_eq_max` bound their heights.
The two local proof adapters are kept inside the existing theorem. Direct
`WellFounded.fix_eq` unfolding preserves all previously published generated
height helpers. The sole new Mathlib import is `Data.Set.Finite.List`, included
in the documented and CI cache selections; the dependency pins stay unchanged.
No executable enumerator is claimed by this semantic finiteness proof.

The bounded-cut adapters reuse core `List.foldl_rel` and `List.foldl_map` for
height monotonicity, `List.nodup_cons` for the repeated root, and Mathlib's
`List.single_le_sum` for strict production-size decrease along a proper subtree.
Core `List.getElem?_set_self`, `List.set_set`, `List.set_getElem_self`, and
`Option.bind_eq_some_iff` prove reversible replacement at the original position.
The height bound reuses `simple_height`, `List.max_le_iff`, and
`List.foldl_max_eq_max`. Existing `Complete.mem_support_iff_subtree`,
`Complete.subtree_context`, `Valid.plug_complete`, and `productionSize_plug`
supply the semantic and accounting bridges. Mathlib has no equivalent adapters
for this project's ordered production-tree syntax. Five immediately proved
structural lemmas suffice; no new syntax, statistic, instance, Mathlib import,
finite-nonterminal hypothesis, or dependency revision is introduced.

Exact decomposition reuses Mathlib's `Nat.strong_induction_on`, generalizing
over the tree rather than its root label. The already proved `bounded_cut`
supplies strict decrease in production-node count and exact reinsertion.
Core `List.mem_append` and `List.mem_singleton` preserve the bounded-cycle
property when appending that final context. Mathlib's generic relation closure
has transitivity, but does not record the context list in this project's
`InsertionSequence` relation. One thin `InsertionSequence.append` adapter proves
concatenation by induction on the existing constructors. No new syntax,
induction principle, statistics, imports, instances, or dependency pins are needed.

The main equality reuses Mathlib's `ContextFreeGrammar.mem_language_iff` and
core set-image membership, together with the existing grammar/tree bridge,
decomposition, first-occurrence activation, and `one_linear`. `List.mem_toFinset`
identifies the distinct context set without identifying contexts with equal
weights. Mathlib has no equivalent for this project's insertion relation;
one proved `InsertionSequence.contextsActivatable` adapter extracts the cycles
from actual insertion steps and reuses `activationOrder_iff_insertionSequence`
and `first_occurrences`. Root selection is local classical choice, so it adds
no public finite or decidable-equality assumption on nonterminals and makes
no claim to implement an activation algorithm. No new imports, definitions,
instances, statistics, or dependency pins are needed.

Forward semilinearity specializes the already proved `bounded_open_finite` to
simple bases using `simple_height` and to bounded cycles using
`Cycle.root_mem_support` and `Valid.support_active`. These two tree-specific
finiteness adapters use `Set.Finite.subset`, with no parallel finiteness theory.
`Set.Finite.toFinset`, `Set.Finite.mem_toFinset`, `Finset.powerset`,
`Finset.mem_powerset`, and `Finset.filter` describe the exact finite family of
activatable components. Mathlib's `IsSemilinearSet.biUnion_finset` and the proved
`component_isLinearSet` bridge supply semilinearity. The public proofs then reuse
`treeRepresentation_eq`, `exists_witness`, and Mathlib's `Language.IsContextFree`
definition. All Mathlib facts are already available through the pinned imports;
the sole new import is the project's `FiniteRepresentation` module. No new
data definitions, instances, cache targets, dependency pins, or nonterminal
assumptions are needed. Classical finite-set selection and filtering establish
semantic existence, with executable construction still a separate obligation.

The expression-image milestone reuses `List.count_flatten`,
`List.count_replicate`, `List.sum_map_eq_nsmul_single`, and
`List.count_eq_one_of_mem` for representative words. `Set.image2_singleton`
proves literal-word matching. `Language.mem_mul` and `append_mem_mul` bridge
concatenation to the existing `counts_append` law; `Set.image_union` handles
finite witness union. `Language.mem_kstar`, `join_mem_kstar`,
`List.eq_replicate_of_mem`, and `AddSubmonoid.mem_closure_singleton` prove the
exact image of a starred word. `Set.range_list_get`,
`AddSubmonoid.closure_union`, and `AddSubmonoid.mem_sup` prove the period product.
`Component.denotation_eq_vadd_closure` recovers the accepted independent indexed
coefficients, including zeros and duplicates. These are thin adapters between
the frozen counting definitions and Mathlib language/closure operations; no
parallel semantics or algebra is introduced. All facts are available through
the existing pinned imports, so no dependency or cache change is needed.
The pinned `RegularExpressions.lean` explicitly lacks regex-to-DFA equivalence,
and `DFA.lean` provides no regular concatenation/star closure. This increment
proved the exact-image half independently. The following milestone completes
DFA regularity and the combined `witnessExpression_correct` theorem.

The DFA-regularity milestone searches `DFA`, `NFA`, `EpsilonNFA`, and
`MyhillNerode` before adding infrastructure. The pinned sources provide
`NFA.toDFA_correct` and regular union, but no word-prefix, concatenation/star
regularity, or equivalent finite continuation-cover lemma. One immediately
proved cover adapter constructs an ordinary Mathlib NFA locally from an existing
finite subtype of languages; `NFA.evalFrom_cons`, `mem_stepSet`, and
`mem_accepts` prove its exact language. `Language.isRegular_iff` reuses universe
lifting for the determinized finite-state DFA. No determinization or automaton
semantics is reproved. Two specialized prefix adapters use the existing DFA's
`acceptsFrom` state languages and `List.tails`, `List.mem_tails`,
`List.suffix_cons`, and finite set images/unions. `Language.mem_mul`,
`one_add_self_mul_kstar_eq_kstar`, and `kstar_one` supply word-prefix and star
semantics. `Language.IsRegular.add` combines the finite witness union. The
existing image and witness bridges finish the converse. A full regex-equivalence
theorem and generic regular concatenation/star development are unnecessary.
`Computability.NFA` and `Data.Set.Finite.Range` are the new Mathlib imports;
NFA adds one cached module to the existing selection, with all dependency pins
unchanged. Classical finite language equality and inclusion establish existence,
not an executable automaton or grammar compiler.

The regular-specialization milestone searches the pinned `Computability` sources
for regular-language/context-free-language inclusion and DFA-to-grammar adapters.
None is present. `DFAGrammar.lean` adds one finite right-linear grammar using
Mathlib's existing `ContextFreeGrammar`, `ContextFreeRule`, `Symbol` and `DFA`.
Finite images and filtering enumerate its transition and accepting-state rules.
The exact bridge reuses `ContextFreeRule.Rewrites.nonterminal_input_mem`,
`Rewrites.input_output`, `ContextFreeGrammar.Produces.single`, `trans_derives`,
`Derives.append_left`, and induction on the existing `Relation.ReflTransGen`.
`DFA.evalFrom_of_append`, input-word evaluation, and `List.map_inj_right` provide
run accounting and terminal-word equality. Specialized shape and invariant
lemmas remain local to `dfaGrammar_derives_iff`; no new rewriting relation,
normalization assumption or generic language inclusion infrastructure is added.
`GrammarImage.lean` shares the already proved exact tree union and semilinearity,
so the frozen public proofs remain at their existing locations without an import
cycle. Six old generated simplifier equalities are retained explicitly because
additional imports change automatic auxiliary-lemma naming. The existing cache
already includes ContextFreeGrammar and DFA; no cache or pin changes are needed.

The executable-activation milestone searches pinned finite-set and computability
sources for enabled-operation/activation search and least-fixed-point algorithms.
Mathlib's order-theoretic fixed-point framework does not provide this finite
operation predicate or the required executable decision interface. The runtime
reuses `Finset.filter`, `biUnion`, union, difference, cardinality and decidable
equality; `Finset.toList` is explicitly noncomputable and is not used to select
runtime operations. Existing `ActivationOrder.filter_of_covered` supplies the
single-operation removal argument; the new monotonicity and batch lemmas only
adapt this project's frozen activation predicate. `Finset.induction_on`,
`mem_erase`, `mem_filter`, `mem_sdiff`, `biUnion_insert`, `coe_union` and
`card_sdiff_of_subset` provide the set and progress proofs. The implementation
uses ordinary structural natural-number recursion with no new data representation,
partial helper, tactic, Mathlib import or cache target. All existing pins remain.

The executable-enumeration milestone searches pinned context-free grammar,
tree and list-product sources. Mathlib has no enumerator for this project's
production-node/hole syntax; `List.sections` already supplies the needed ordered
Cartesian products. `List.mem_sections`, `forall₂_map_right_iff`,
`forall₂_and_left`, `forall₂_map_left_iff` and `forall₂_eq_eq_eq` turn product
membership into child membership and exact ordered root matching.
`List.finRange` and `mem_finRange` supply concrete declared leaf lists;
`List.mem_map`, `mem_flatMap`, `mem_filter` and `mem_toFinset` connect generated
nodes to decoded grammar rules, including duplicate productions.
Core `List.foldl_max_eq_max`, `le_max_of_mem` and `max_le_iff` provide height
accounting. The new height, root-product and validity lemmas specialize existing
list laws to the frozen tree syntax. No new tree representation or instance is
introduced. Both runtime definitions have no axiom dependencies and use explicit
natural-number recursion without partial helpers. `Mathlib.Data.List.Sections`
is the sole new import/cache target, added to CI and the build guide; all pins
and proof allowlists remain unchanged.

The quantitative-family milestone searches pinned finite-set, finite-function,
list-sum and occurrence-count sources. Mathlib supplies finite function-space
cardinalities (used through `simp`), `Finset.card_image_le`, `card_union_le`,
`card_biUnion_le`, `sum_le_sum`, `card_filter_le`, `le_sup`, and natural-power
monotonicity. These count production child tuples without another tree datatype
or a separate cardinality theory. Core `List.ofFn_getElem` and list extensionality
recover an ordered tuple from an existing child list. `Finset.sum_range_succ'`
and `mul_sum` give the geometric position recurrence. `List.sum_le_length_nsmul`
bounds child-yield sums, while `List.sum_toFinset_count_eq_length`,
`Finset.sum_subset` and `List.count_eq_zero` identify total weight with yield
length. New cover/height adapters specialize these laws to the frozen tree
syntax; they are proof support, distinct from the executable enumerator. The
existing generated tree equations supply the height and yield formulas, and
the new strict child-height lemma avoids reproving the later enumeration equivalence.
No new Mathlib import/cache target, instance, project axiom or partial helper
is needed; the pins remain unchanged.

The bounded-witness milestone searches pinned finite-product, powerset,
finite-list and finite-sum sources. `Finset.card_product`, `card_powerset` and
`card_filter_le` bound candidate components. `List.length_map` and
`Finset.length_toList` count indexed periods without collapsing equal weights.
`List.mem_map`, `Finset.mem_toList`, `mem_filter`, `mem_product` and
`mem_powerset` connect listed components to their base/context identities.
The existing `treeRepresentation_correct` supplies exact semantic equality;
no new grammar or semilinearity proof is needed. `Finset.sum_apply`,
`sum_add_distrib`, `sum_comm` and `sum_le_sum` supply norm accounting, while
natural-power/product monotonicity enlarges the family budgets. The five named
adapters specialize these existing laws to the frozen witness and activation
predicates. No new Mathlib import/cache target, datatype, instance or partial
runtime helper is added. Classical finite-set listing/filtering is explicitly
separate from the executable compiler described below; the pins remain unchanged.

The bit-budget milestone reuses the already imported `Mathlib.Data.Nat.Log`.
`Nat.le_pow_clog` supplies the ceiling-log power bound, and
`Nat.pow_le_pow_right` enlarges the exponent to the accepted minimum width.
`Finset.single_le_sum` bounds a coordinate by its vector norm.
`List.sum_le_length_nsmul`, `Nat.nsmul_eq_mul` and natural-product monotonicity
bound all listed entry widths. Local proof facts specialize these laws to
`WithinBounds`; no named helper, new import/cache target, instance or runtime
definition is introduced. The fixed-width definitions and pins are unchanged.

The executable-compiler milestone searches the pinned list equality, sublists,
deduplication, finite-cardinality and additive-closure sources. Core
`List.isEqv` supplies ordered child comparison; explicit `Nat.rec` avoids new
nested-recursion runtime helpers. A direct tree recursor is unavailable to the
code generator, so a certified height-budget comparison supplies equality for
the existing datatype. No second syntax datatype or global equality instance is
introduced. `List.dedup`, `mem_dedup`, `nodup_dedup`, `mem_sublists`,
`length_sublists`, `Sublist.nodup`, `Sublist.length_le`, `List.mem_filter` and
`length_filter_le` provide unique syntax families and exhaustive subsets.
`List.toFinset_card_of_nodup`, `Finset.card_le_univ`, `List.le_max_of_mem` and
`List.foldl_max_eq_max` connect declared syntax to the existing counting cover.
`List.sum_toFinset` and `Component.denotation_eq_vadd_closure` transfer component
denotation across arbitrary duplicate-free context listing without comparing
weights. `Subsingleton.elim` reconciles equality decisions in proofs; runtime
uses the explicit computable finite/syntax decisions. The compiler reuses
`boundedEnumeration`, `activationTest`, `treeRepresentation_correct`,
`card_treeFamily_le`, `yield_length_le_heightPositions`,
`contextComponent_size_bounds` and `witness_bit_bound` rather than repeating
those mathematical developments. All 31 named additions are executable adapters
or their necessary certification/budget results. No new Mathlib import/cache
target, datatype, global instance, project axiom, partial helper or pin change is
needed. Classical finite-set listing remains confined to the existence proof;
the implementing `compiler` executes list assembly.

No trace-membership dependency, replacement semilinearity predicate, or generic
automata-equivalence development is introduced. Re-audit Mathlib before adding
helpers in each accepted proof milestone; these identified gaps are not permission
to duplicate unrelated infrastructure.
