# Audit of the pinned Mathlib

Lean 4.34.1; Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`
(release v4.34.1). The dependency manifest records all eight transitive packages.
The audit searched the actual sources before choosing the interfaces.

| Existing source | Reuse and remaining gap |
| --- | --- |
| `Computability/Language.lean` | Reuse `Language`, `Symbol`, and language algebra. No parallel language datatype. |
| `Computability/ContextFreeGrammar.lean` | Reuse `ContextFreeRule`, `ContextFreeGrammar`, `Produces`, `Derives`, `language`, `Language.IsContextFree`. Rewriting context lemmas already exist. No ordered derivation-tree syntax or complete-tree equivalence was found. |
| `ModelTheory/Arithmetic/Presburger/Semilinear/Defs.lean` | Reuse `IsLinearSet`, `IsSemilinearSet`, finitely generated additive closure, and finite-union lemmas. New witness records only supply explicit indexed bases/periods; their denotation-to-Mathlib bridges are obligations. |
| `Data/List/Count.lean` and finite-sum infrastructure | Reuse `List.count`, lists, `Fin`, `Finset`, natural scalar multiplication and sums. No custom vector arithmetic. |
| `Computability/RegularExpressions.lean` | Reuse concrete `RegularExpression` constructors and `matches'`. The source explicitly reports no general equivalence with DFAs/NFAs. This project needs only regularity of the constructed finite unions of `u v₁* … vₖ*`; a full equivalence theorem is unnecessary. |
| `Computability/DFA.lean`, `NFA.lean`, `EpsilonNFA.lean` | Reuse `Language.IsRegular`, `NFA.toDFA_correct` and `εNFA.toNFA_correct` where applicable. A specialized finite automaton for the witness expressions can avoid reproving determinization. The converse does not require a grammar. |
| `Data/Nat/Log.lean` | Reuse `Nat.clog` for the document's fixed-width bit bound. |
| `Data/Tree/Basic.lean`, `Data/W/*` | Existing binary trees/W-types do not directly provide ordered variable-arity production nodes, nonterminal holes, local RHS-root matching or grammar semantics. A small raw syntax with a separate validity predicate keeps these meanings explicit. |

No trace-membership dependency, replacement semilinearity predicate, or generic
automata-equivalence development is introduced. Re-audit Mathlib before adding
helpers in each accepted proof milestone; these identified gaps are not permission
to duplicate unrelated infrastructure.
