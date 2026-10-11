# A guided proof of Parikh's theorem

Parikh's theorem says that the letter counts of a context-free language form a
finite union of linear sets. The key question is: **where do the bases and periods
come from?** In this proof, bases come from small derivation trees, and periods
come from pieces of trees that can be inserted repeatedly.

This guide explains the argument before the Lean details. It follows the
repository's [mathematical exposition](../reference/parikh_theorem.pdf) and the
derivation-tree approach discussed by [Sin'ya (2019)](https://arxiv.org/abs/1909.09393)
and [Rubtsov (2022)](https://arxiv.org/abs/2301.00047). The
[README references](../README.md#references) distinguish these presentations from
Parikh's original paper. The [proof plan](PROOF_PLAN.md) provides the detailed
source-to-declaration map; the [status ledger](PROOF_STATUS.md) records unfinished
work. The example below is a mathematical illustration, not an additional
machine-checked example in the library.

## 1. Counting turns concatenation into addition

For a word $w$, write $\Psi(w)$ for its vector of letter counts. For example,
with coordinates ordered as $(a,b,c)$, both `acb` and `abc` have vector $(1,1,1)$.
The essential identity is

$$\Psi(uv)=\Psi(u)+\Psi(v).$$

Consequently, inserting a fixed piece of a derivation adds a fixed vector,
regardless of where its terminal letters appear in the word. Repeated insertions
are the source of natural-number multiples of period vectors.

In Lean, [Counting.lean](../Parikh/Counting.lean) defines `counts` and proves
`counts_append`. A `Component` consists of a base vector and a list of periods.
Its `denotation` assigns an independent natural coefficient to each list entry.
Every Lean list is finite, so the datatype already supplies the required
finiteness. A `Witness` is a finite list of components, interpreted as their union.

## 2. A running grammar

Consider the grammar with start symbol $S$ and productions

$$S\to aASb\mid\varepsilon,\qquad A\to cA\mid\varepsilon.$$

Every use of the first $S$ production contributes one `a`, one `b`, and a place
where some `c`s may be generated. The empty word is possible. Every other word
has equally many `a`s and `b`s, at least one of each, and any number of `c`s.
Its Parikh image is therefore

$$\{(0,0,0)\}\;\cup\;
\{(1,1,0)+n(1,1,0)+k(0,0,1)\mid n,k\in\mathbb N\}.$$

We will recover this description by manipulating trees. The example also
explains why a list of available period vectors alone is not enough: a context
that adds `c` needs an occurrence of $A$ before it can be inserted.

## 3. Trees can describe unfinished derivations

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
$S\to\varepsilon$ thus has support $\{S\}$, despite producing no letters. Holes
contribute no support. These conventions are defined in
[GrammarTrees.lean](../Parikh/GrammarTrees.lean).

## 4. Cycles are repeatable contexts

A cycle context has one hole, with the same nonterminal as its root, and at least
one production node. Filling that hole with a matching subtree produces a larger
tree with the same root. Repeating this operation inserts another copy of the
context each time.

For our grammar, choose these two contexts:

| Context | Construction | Required root | Added support | Weight in $(a,b,c)$ |
| --- | --- | --- | --- | --- |
| $C$ | Use $S\to aASb$, expand $A\to\varepsilon$, and leave the $S$ child as a hole. | $S$ | $\{S,A\}$ | $(1,1,0)$ |
| $E$ | Use $A\to cA$ and leave the final $A$ as a hole. | $A$ | $\{A\}$ | $(0,0,1)$ |

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

## 5. Why activation comes before independent repetition

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

$$
\operatorname{wt}(B)+\sum_{C\in D}\operatorname{wt}(C)
+\left\{\sum_{C\in D}k_C\operatorname{wt}(C)\mid k_C\in\mathbb N\right\}.
$$

The first sum accounts for the compulsory first copy of each chosen context.
The second accounts for arbitrary extra copies. This is the content of
`one_linear`.

For our chosen base and contexts, the three possible families give:

| Selected family | Vectors obtained |
| --- | --- |
| $\varnothing$ | $(0,0,0)$ |
| $\{C\}$ | $(1,1,0)+n(1,1,0)$ |
| $\{C,E\}$ | $(1,1,1)+n(1,1,0)+k(0,0,1)$ |

The family $\{E\}$ is unavailable from this base. The last two rows together
are the nonempty-word component in Section 2. This small example admits a
simplified witness; the general tree construction can produce additional,
overlapping components and does not promise a minimal representation.

## 6. Why finitely many bases and cycles suffice

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

## 7. The equality has two directions

`treeRepresentation_eq` in [Statements.lean](../Parikh/Statements.lean) joins
the argument together:

- Given a vector in a component, activate its contexts, insert the requested
  extra copies, and read the resulting complete tree. Its word belongs to the
  grammar language and has exactly that vector.
- Given a word in the grammar language, take its derivation tree, decompose it,
  and retain the distinct contexts used. Their first occurrences give an
  activation order, so the word's vector belongs to the corresponding component.

This proves an exact description of the image. Applying the finite-union result
gives `grammar_image`; the Mathlib language interface gives `contextFree_image`.
`grammar_witness` then expresses semilinearity as a finite list of components.

## 8. Returning from vectors to words

The converse is simpler mathematically. Fix an order of the terminal alphabet
and represent a vector by blocks of letters in that order. For a base $b$ and
periods $p_1,\ldots,p_r$, use the regular expression

$$u_b(u_{p_1})^*\cdots(u_{p_r})^*.$$

Its count vectors are exactly the linear component: each star chooses the
coefficient of one period. A finite union realizes a semilinear witness.
[RegularRealization.lean](../Parikh/RegularRealization.lean) proves these image
identities. [WordBlockAutomata.lean](../Parikh/WordBlockAutomata.lean) supplies
finite automata for the required word-prefix operations, reusing Mathlib's NFA
determinization. This connects the expressions to Mathlib's DFA regularity
predicate and proves `converse`.

Combining the converse with the forward theorem gives `regular_realization`:
every grammar has a regular language with the same letter counts. The words
need not occur in the same order in those two languages.

The existence proofs use classical reasoning. Computing a witness from a finite
grammar encoding, together with proved resource bounds, is a further obligation.
[Construction.lean](../Parikh/Construction.lean) specifies those requirements;
the [status ledger](PROOF_STATUS.md) distinguishes them from the completed
semantic results.
