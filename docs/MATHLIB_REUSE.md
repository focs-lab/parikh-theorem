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
| `Computability/DFA.lean`, `NFA.lean`, `EpsilonNFA.lean` | Reuse `Language.IsRegular`, `NFA.toDFA_correct` and `εNFA.toNFA_correct` where applicable. A specialized finite automaton for the witness expressions can avoid reproving determinization. The converse does not require a grammar. |
| `Data/Nat/Log.lean` | Reuse `Nat.clog` for the document's fixed-width bit bound. |
| `Data/Set/Finite/List.lean` | Reuse `List.finite_length_eq` over a finite subtype for production child lists, with finite images and unions for bounded-tree finiteness. No parallel list-enumeration or generic tree-finiteness theory. |
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

No trace-membership dependency, replacement semilinearity predicate, or generic
automata-equivalence development is introduced. Re-audit Mathlib before adding
helpers in each accepted proof milestone; these identified gaps are not permission
to duplicate unrelated infrastructure.
