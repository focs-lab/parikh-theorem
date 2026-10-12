# A guided proof of Parikh's theorem

The proof constructs the bases and periods of a semilinear set from derivation
trees: small complete trees provide bases, and repeatable contexts provide
periods. We will follow this construction through a grammar where inserting one
context enables another.

The guide follows the [mathematical reference](../reference/parikh_theorem.pdf).
The [proof map](../maintenance/proof-map.md) connects its steps to Lean declarations.

## Counting turns concatenation into addition

For a word $w$, write $\Psi(w)$ for its vector of letter counts. For example,
with coordinates ordered as $(a,b,c)$, both `acb` and `abc` have vector $(1,1,1)$.
The essential identity is

```math
\Psi(uv)=\Psi(u)+\Psi(v).
```

Consequently, inserting a fixed piece of a derivation adds a fixed vector,
regardless of where its terminal letters appear in the word. Repeated insertions
are the source of natural-number multiples of period vectors.

In Lean, `parikhVector` counts letters and `parikhVector_append` gives this
identity. A `LinearComponent` consists of a base vector and a list of periods.
Its `denotation` assigns an independent natural coefficient to each list entry.
A `SemilinearRepresentation` is a finite list of components, interpreted as
their union. See the [API](API.md) for these definitions.

## A running grammar

Consider the grammar with start symbol $S$ and productions

```math
S\to aASb\mid\varepsilon,\qquad A\to cA\mid\varepsilon.
```

Every use of the first $S$ production contributes one `a`, one `b`, and a place
where some `c`s may be generated. The empty word is possible. Every other word
has equally many `a`s and `b`s, at least one of each, and any number of `c`s.
Its Parikh image is therefore

```math
\lbrace (0,0,0)\rbrace\;\cup\;
\lbrace (1,1,0)+n(1,1,0)+k(0,0,1)\mid n,k\in\mathbb N\rbrace.
```

We will recover this description by manipulating trees. The example also
explains why a list of available period vectors alone is not enough: a context
that adds `c` needs an occurrence of $A$ before it can be inserted.

## Trees can describe unfinished derivations

A `ParseTree` has three kinds of node: a terminal leaf, a nonterminal hole, or a
production node with an ordered list of children. A hole records a place where
a derivation has not yet been filled in.

`Valid g t` checks that production nodes use rules of `g` and that their child
roots match the right-hand sides. `Complete g t` additionally requires no holes.
A complete tree rooted at the start symbol derives its terminal yield. The
`derives_iff_tree` theorem connects this description to Mathlib's derivations.

The empty production $S\to\varepsilon$ deserves care. Its tree is a production
node with no children. Its frontier and yield are empty, but its production
size and height are both one. It is different from a hole labelled $S$, which
still awaits expansion and has production size and height zero.

The **support** of a tree consists of its production-node labels. The tree for
$S\to\varepsilon$ thus has support $\lbrace S\rbrace$, despite producing no letters. Holes
contribute no support. These conventions are defined in
[GrammarTrees.lean](../Parikh/GrammarTrees.lean).

## Cycles are repeatable contexts

A cycle context has one hole, with the same nonterminal as its root, and at least
one production node. Filling that hole with a matching subtree produces a larger
tree with the same root. Repeating this operation inserts another copy of the
context each time.

For our grammar, choose these two contexts:

| Context | Construction | Required root | Added support | Weight in $(a,b,c)$ |
| --- | --- | --- | --- | --- |
| $C$ | Use $S\to aASb$, expand $A\to\varepsilon$, and leave the $S$ child as a hole. | $S$ | $\lbrace S,A\rbrace$ | $(1,1,0)$ |
| $E$ | Use $A\to cA$ and leave the final $A$ as a hole. | $A$ | $\lbrace A\rbrace$ | $(0,0,1)$ |

Start with the complete base $B$ consisting of $S\to\varepsilon$. Inserting $C$
around it gives a tree for `ab`; inserting $E$ around the newly present
$A\to\varepsilon$ subtree gives a tree for `acb`.

Insertion retains the original subtree inside the hole. Its support is therefore
preserved, and the context's support is added. Its weight increases by precisely
the context's weight. These are `insertion_enabled` and `insertion_accounting`
in [Decomposition.lean](../Parikh/Decomposition.lean), built from the plugging
and replacement lemmas.

A context may have zero weight. For instance, in a grammar with $A\to A$, that
production above a hole is a cycle which adds a production but no letters. This
is why terminal word length cannot measure progress when we remove cycles.

## Why activation comes before independent repetition

In the base $B$, only $S$ is present. Context $C$ is enabled immediately, but
$E$ is not. After inserting $C$, an $A$ production node exists, so $E$ becomes
enabled. Thus $C,E$ is an activation order, whereas $E,C$ is not.

The abstract definitions in [Activation.lean](../Parikh/Activation.lean) retain
just this information. An operation requires one label and adds a set of labels.
An `ActivationOrder` is a list whose operations are enabled successively.
`Activatable` says a finite family has such an order using each member once.

Two observations turn this into a linear set. First, later occurrences of an
operation can be omitted when finding an activation order: their added labels
are already present from its first occurrence. Second, after the first-use pass,
all selected cycle contexts remain enabled, so any extra multiplicities are
possible. These are `first_occurrences` and `positive_multiplicities`.

For a fixed complete base $B$ and activatable set $D$, the resulting component is

```math
\operatorname{wt}(B)+\sum_{C\in D}\operatorname{wt}(C)
+\left\lbrace \sum_{C\in D}k_C\operatorname{wt}(C)\mid k_C\in\mathbb N\right\rbrace.
```

The first sum accounts for the compulsory first copy of each chosen context.
The second accounts for arbitrary extra copies. This is the content of
`one_linear`.

For our chosen base and contexts, the three possible families give:

| Selected family | Vectors obtained |
| --- | --- |
| $\varnothing$ | $(0,0,0)$ |
| $\lbrace C\rbrace$ | $(1,1,0)+n(1,1,0)$ |
| $\lbrace C,E\rbrace$ | $(1,1,1)+n(1,1,0)+k(0,0,1)$ |

The family $\lbrace E\rbrace$ is unavailable from this base. The last two rows together
give the nonempty-word component of the running grammar. Other bounded contexts
can give overlapping components.

## Why finitely many bases and cycles suffice

The argument so far describes what a chosen family can produce. We must also
show that every complete tree can be reconstructed from bounded pieces.

A tree is **simple** when no production label repeats along a downward path.
Let $h$ be the number of active nonterminals: those mentioned in grammar rules,
together with the start symbol. A simple valid tree has height at most $h$.
This remains true if the ambient Lean type of nonterminals is infinite, because
the finite grammar mentions only finitely many of them.

In a non-simple tree, choose a minimal non-simple subtree. Its children are
simple. A repeated root label on a path identifies a removable cycle; the
simple children also bound its side branches. The resulting cycle has height
at most $h+1$. Removing it strictly decreases the number of production nodes.

Strong induction on this number eventually reaches a simple complete tree.
Recording the cuts in reverse gives an insertion sequence reconstructing the
original tree exactly. See `bounded_cut` and `decomposition` in
[Decomposition.lean](../Parikh/Decomposition.lean), with the selection argument
in [BoundedCutSupport.lean](../Parikh/BoundedCutSupport.lean).

Finite terminals, finitely many productions, bounded branching, restricted hole
labels, and bounded height give finitely many possible trees. Thus there are
finitely many bases and bounded cycles, and finitely many context subsets.
[FiniteRepresentation.lean](../Parikh/FiniteRepresentation.lean) combines these
facts with `one_linear` to establish semilinearity.

## The equality has two directions

`treeRepresentation_correct` in [GrammarImage.lean](../Parikh/GrammarImage.lean)
joins the argument together. Its equality is exposed as `treeRepresentation_eq`
in [Statements.lean](../Parikh/Statements.lean):

- Given a vector in a component, activate its contexts, insert the requested
  extra copies, and read the resulting complete tree. Its word belongs to the
  grammar language and has exactly that vector.
- Given a word in the grammar language, take its derivation tree, decompose it,
  and retain the distinct contexts used. Their first occurrences give an
  activation order, so the word's vector belongs to the corresponding component.

Applying the finite-union result proves that the image is semilinear.
The public theorem is `parikhImage_isSemilinear_of_grammar`; its language-level
form is `parikhImage_isSemilinear_of_isContextFree`.
`exists_semilinearRepresentation_of_grammar` gives the finite representation.

## Returning from vectors to words

The converse is simpler mathematically. Fix an order of the terminal alphabet
and represent a vector by blocks of letters in that order. For a base $b$ and
periods $p_1,\ldots,p_r$, use the regular expression

```math
u_b(u_{p_1})^*\cdots(u_{p_r})^*.
```

Its count vectors are exactly the linear component: each star chooses the
coefficient of one period. A finite union realizes a semilinear witness.
[RegularRealization.lean](../Parikh/RegularRealization.lean) proves these image
identities. [WordBlockAutomata.lean](../Parikh/WordBlockAutomata.lean) supplies
finite automata for the required word-prefix operations, reusing Mathlib's NFA
determinization. This connects the expressions to Mathlib's DFA regularity
predicate. The result is `exists_regularLanguage_with_parikhImage`.

Combining this with the forward theorem gives
`exists_regularLanguage_with_grammar_parikhImage`: every grammar has a regular
language with the same letter counts, although the order of letters may differ.

## Why regular languages also have semilinear images

The converse starts from a semilinear set and produces a regular language.
The theorem `parikhImage_isSemilinear_of_isRegular` starts with any DFA-regular
language and proves that its image is semilinear. To reuse the forward theorem,
interpret the DFA as a right-linear grammar.

Each state becomes a nonterminal. A transition $q \xrightarrow{a} q'$ becomes
$q\to a q'$, and an accepting state has an empty production $q\to\varepsilon$.
A partial derivation records the letters already read, followed by the current
state. It can finish precisely when that state is accepting.
[DFAGrammar.lean](../Parikh/DFAGrammar.lean) proves that the grammar and DFA accept
exactly the same words. The shared forward result in `GrammarImage.lean` then
gives semilinearity.

## Computing the representation

For finite encoded input, `compileGrammar` carries out the tree construction.
It enumerates valid trees through a height bound, filters the base and cycle
families, and tests activation for each candidate context subset.

The activation test repeatedly processes all enabled contexts, adds their
supports, and removes them from the remaining work. It succeeds when none
remain, and fails if it stalls. Processing any enabled context first preserves
whether an activation order exists, which justifies the test. For each accepted
base and subset, the compiler pays for one copy of each context in the base and
retains its weight as a period.

For quantitative bounds, let $n$ count nonterminals, $d$ terminals, $p$
productions, and $b$ the maximum right-hand-side length, with a minimum of one.
At height $n+1$, put

```math
M=\sum_{i=0}^{n+1}b^i,\qquad K=(1+d+n+p)^M.
```

There are at most $K$ bases and $K$ contexts, each with terminal-weight norm at
most $M$. Thus the representation has at most $K2^K$ components, each with at
most $K$ periods. A component's base has norm at most $(K+1)M$, and every period
has norm at most $M$.

Every coordinate is at most its vector's norm. A width of
$L=\max(1,\lceil\log_2((K+1)M+1)\rceil)$ bits therefore fits every coordinate.
The total numerical entry budget is $K2^K(K+1)dL$ bits.

`compileGrammar_correct`, `compileGrammar_size_bounds`, and
`compileGrammar_bit_bound` prove these guarantees for the computed output.
The [compiler guide](COMPILER.md) shows how to execute it; the
[proof map](../maintenance/proof-map.md) locates the enumeration and bound proofs.
