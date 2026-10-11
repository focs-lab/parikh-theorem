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

No trace-membership dependency, replacement semilinearity predicate, or generic
automata-equivalence development is introduced. Re-audit Mathlib before adding
helpers in each accepted proof milestone; these identified gaps are not permission
to duplicate unrelated infrastructure.
