# Specification of the Plonkish Relation

## Objectives
- Need to agree on the API between “zkInterface for Plonkish” and the proving system.  Specify a general statement that the proving system has to implement.
- Section 2 of [[Thomas 2022]](https://eprint.iacr.org/2022/777.pdf) : describes high level API of zk Interface for Plonkish statements.

This is intended to be read in conjunction with the [Plonkish Backend Optimizations](optimizations.md) document, which describes how to compile the abstract constraint system described here into a concrete circuit.

## Dependencies and notation

Plonkish arithmetization depends on a field over a prime modulus $p$. Integers taken modulo the field modulus $p$ are called field elements and their type is denoted as $\F$; arithmetic operations on field elements are implicitly performed modulo $p$. We denote the additive identity by $0$ and the multiplicative identity by $1$.  We denote the sum, difference, and product of two field elements using the $+$, $-$, and $\cdot$ operators, respectively.

$\N$ refers to the type of natural numbers, and $\Z$ to the type of integers.

The notation $\range{a}{b}$ means the vector of integers from $a$ (inclusive) to $b$ (exclusive) in ascending order.

The notation $x \typecolon T$ means that $x$ is of type $T$.

$T \times U$ means the type of pairs with first element from the type $T$, and second element from the type $U$.

$T \to U$ means the type of functions with range type $T$ and domain type $U$.

$[n]$ means the type of natural numbers from $0$ (inclusive) to $n$ (exclusive).

$T^{[m]}$ means the type of vectors indexed by $[m]$ with elements from type $T$.

$T^{[m \times n]}$ means the type of matrices indexed first by a column index in $[m]$ and then by a row index in $[n]$, with elements from type $T$. That is, if $w \typecolon T^{[m \times n]}$ then $w[i, j]$ means the element at column index $i \typecolon [m]$ and row index $j \typecolon [n]$.

If $X$ is a field element, on the other hand, then $X^e$ means the result of raising $X$ to the integer power $e$. There are no square brackets around the exponent in this case.

The length of a vector $S$, or the number of elements in a set $S$, is written $\#S$.

The condition that $e$ is a member of the set $S$ is written $e \in S$.

$\Set{T}$ means the type of sets with elements in $T$.

$\Equiv{T}$ means the type of equivalence relations (i.e. reflexive, symmetric, and transitive binary relations) on $T$.

$\vector{f(e)}{e \gets \range{a}{b}}$ means the vector of evaluations of $f$ on $\range{a}{b}$.

$\vector{f(e)}{e}$ means the vector of evaluations of $f$ for some implicitly defined vector of zero-based indices $e$.

$\displaystyle\sum_{i \stypecolon T} x_i$ means the sum of field elements $x_i$ for all $i \typecolon T$, and $\displaystyle\prod_{i \stypecolon T} x_i$ means the corresponding product. 

$\implies$ means logical implication.

When $f$ is a function that takes a tuple as argument, we will allow $f((i, j))$ to be written as $f[i, j]$.

The terminology used here is intended to be consistent with the [ZKProof Community Reference](https://docs.zkproof.org/reference). We diverge from this terminology as follows:
* We refer to the public inputs to the circuit as an "instance vector". The entries of this vector are called "instance variables" in the Community Reference.

## The General Plonkish Relation $\R_\plonkish$

The general relation $\R_\plonkish$ contains pairs of $(x, w)$ where:
* the instance $x$ consists of the parameters of the proof system, the circuit $C$, and the public inputs to the circuit (i.e. the instance vector).
* the witness $w$ consists of the matrix of values provided by the prover. In this model it consists of the (potentially private) prover inputs to the circuit, and any intermediate values (including fixed values) that are not inputs to the circuit but are required in order to satisfy it.

We say that a $x$ is a *valid* instance whenever there exists some witness $w$ such that $(x, w) \in \R_\plonkish$ holds.
The Plonkish language $\L_\plonkish$ contains all valid instances.

A circuit-specific relation is a specialization of $\R_\plonkish$ to a particular circuit.

If the proof system is knowledge sound, then the prover must have knowledge of the witness in order to construct a valid proof. If it is also zero knowledge, then witness entries can be private, and an honestly generated proof leaks no information about the private inputs to the circuit beyond the fact that it was obtained with knowledge of some satisfying witness.

### Instances

The relation $\R_\plonkish$ takes instances of the following form:

| Instance element                         | Description                                | <div style="width: 0em"></div> |
| ---------------------------------------- |:------------------------------------------ | ------------------------------ |
| $\untyped{\F}$                           | A prime field.                                                              |
| $\untyped{C}$                            | The circuit.                                                                |
| $\typed{\phi}{\F^{[C.t]}}$               | The instance vector, where $t$ is the instance vector length defined below. |

The circuit $C \typecolon \mathsf{AbstractCircuit}_{\F}$ in turn has the following form:

| Circuit element                          | Description                                                                                             | <div style="width: 9.5em">Used in</div>   |
| ---------------------------------------- |:------------------------------------------------------------------------------------------------------- |:----------------------------------------- |
| $\typed{t}{\N}$                          | Length of the instance vector.                                                                          |                                           |
| $\typed{n}{\N \where n > 0}$             | Number of rows for the witness matrix.                                                                  |                                           |
| $\typed{m}{\N \where m > 0}$             | Number of columns for the witness matrix.                                                               |                                           |
| $\typed{≡}{\Equiv{[m]\!\times\![n]}}\bs$ | An equivalence relation indicating which witness entries are equal to each other.                       | [Copy constraints](#copy-constraints)     |
| $\typed{S}{([m]\!\times\![n])^{[t]}}$    | A set indicating which witness entries are equal to instance vector entries.                            | [Copy constraints](#copy-constraints)     |
| $\typed{m_f}{\N \where m_f ≤ m}$         | Number of columns that are fixed.                                                                       | [Fixed constraints](#fixed-constraints)   |
| $\typed{f}{\F^{[m_f \times n]}}$         | The fixed content of the first $m_f$ columns.                                                           | [Fixed constraints](#fixed-constraints)   |
| $\typed{p_u}{\F^{[m]} \to \F}$           | Custom multivariate polynomials.                                                                        | [Custom constraints](#custom-constraints) |
| $\typed{\CUS_u}{\Set{[n]}}$              | Sets indicating rows on which the custom polynomials $p_u$ are constrained to evaluate to $0\stop$      | [Custom constraints](#custom-constraints) |
| $\typed{L_v}{\N}$                        | Number of table columns in the lookup table with index $v\stop$                                         | [Lookup constraints](#lookup-constraints) |
| $\typed{\TAB_v}{\Set{\F^{[L_v]}}}$       | Lookup tables $\TAB_v$ each containing a set of vectors of type $\F^{[L_v]}\stop$                       | [Lookup constraints](#lookup-constraints) |
| $\typed{q_{v,s}}{\F^{[m]} \to \F}$       | Scaling multivariate polynomials $q_{v,s}$ for $s \typecolon [L_v]\stop$                                | [Lookup constraints](#lookup-constraints) |
| $\typed{\LOOK_v}{\Set{[n]}}$             | Sets indicating rows on which the scaling polynomials $q_{v,s}$ evaluate to some tuple in $\TAB_v\stop$ | [Lookup constraints](#lookup-constraints) |

Multivariate polynomials are defined below in the [Custom constraints](#custom-constraints) section.

### Witnesses

The relation $\R_\plonkish$ takes witnesses of the following form:

| Witness element                          | Description                                | <div style="width: 0em"></div> |
| ---------------------------------------- |:------------------------------------------ | ------------------------------ |
| $\typed{w}{\F^{[m \times n]}}$           | The witness matrix.$\hspace{6em}$                                           |

Define $\vec{w}_j$ as the row vector $\vector{w[i, j]}{i \leftarrow \range{0}{m}}$.

### Definition of the relation

Given the above definitions, the relation $\R_\plonkish$ corresponds to a set of $\kern0.1em(\textsf{instance},\,\textsf{witness})\kern0.1em$ pairs $(x, w)$ where
$$
x = \left(\F,\ C = \left(t, n, m, \kern-0.1em\equiv, S, m_f, f,\ \vector{(p_u, \mathsf{CUS}_{u})}{u}\!,\,\vector{(L_v, \mathsf{TAB}_v, \vector{q_{v,s}}{s}\!, \mathsf{LOOK}_v)}{v}\right)\!,\, \phi\right)
$$
such that:
$$
\begin{array}{ll|l}
   w \typecolon \F^{[m \times n]}\comma f \typecolon \F^{[m_f \times n]} & & i \typecolon [m_f]\comma j \typecolon [n] \implies w[i, j] = f[i, j] \\[0.3ex]
   S \typecolon \Set{([m] \times [n]) \times [t]}\comma \phi \typecolon \F^{[t]} & & ((i,j),k) \in S \implies w[i, j] = \phi[k] \\[0.3ex]
   \equiv\,\,\typecolon \Equiv{[m] \times [n]} & & (i,j) \equiv (k,\ell) \implies w[i, j] = w[k, \ell] \\[0.3ex]
   \mathsf{CUS}_u \typecolon \Set{[n]}\comma p_u \typecolon \F^{[m]} \to \F & & j \in \mathsf{CUS}_u \implies p_u(\vec{w}_j) = 0 \\[0.3ex]
   \mathsf{LOOK}_v \typecolon \Set{[n]}\comma q_{v,s} \typecolon \F^{[m]} \to \F\comma \mathsf{TAB}_v \typecolon \Set{\F^{[L_v]}} & & j \in \mathsf{LOOK}_v \implies \vector{q_{v,s}(\vec{w}_j)}{s \gets \range{0}{L_v}} \in \mathsf{TAB}_v
\end{array}
$$

In this model, a circuit-specific relation $\mathcal{R}_{\F, C}$ for a field $\F$ and circuit $C$ is the relation $\R_\plonkish$ restricted to the subset of instances and witnesses $((\F, C, \phi \typecolon \F^{[C.t]}),\ w \typecolon \F^{[C.m \times C.n]})$.

### Conditions satisfied by statements in $\R_\plonkish$

There are four types of constraints that a Plonkish statement $(x, w) \in \mathcal{R}_{\mathsf{Plonkish}}$ must satisfy:

* Fixed constraints
* Copy constraints
* Custom constraints
* Lookup constraints

#### Fixed constraints

The first $m_f$ columns of $w$ are fixed to the columns of $f$.

#### Copy constraints

Copy constraints enforce that entries in the witness matrix are equal to each other, or that an instance entry is equal to a witness entry.

| Copy Constraints                                        | Description                                                                                                       |
|:------------------------------------------------------- |:----------------------------------------------------------------------------------------------------------------- |
| $((i,j),k) \in S \implies$ $w[i, j] = \phi[k]$          | The advice entry at row $i$ and column $j$ is equal to the instance entry at index $k$ for all $((i,j),k) \in S$. |
| $(i,j) \equiv (k,\ell) \implies$ $w[i, j] = w[k, \ell]$ | $\equiv$ is an equivalence relation indicating which witness entries are constrained to be equal.                 |

By convention, when fixed abstract cells have the same value, we consider them to be equivalent under $\equiv$. That is,

$i < m_f$ and $k < m_f$ and $f[i, j] = f[k, \ell] \implies (i, j) \equiv (k, \ell)$

This has no direct effect on the relation, but it will simplify expressing an [optimization](optimizations.md).

#### Custom constraints

Plonkish also allows custom constraints between the witness matrix entries. In the abstract model we are defining, a custom constraint applies only within a single row of the witness matrix, for the rows that are selected for that constraint.

In some systems using Plonkish, custom constraints are referred to as "gates".

Custom constraints enforce that witness entries within a row satisfy some multivariate polynomial. Here $p_u$ could indicate any case that can be generated using a combination of multiplications and additions.

| Custom Constraints | Description |
|:------------------ |:----------- | 
| $j \in \mathsf{CUS}_u \implies$ $p_u(\vec{w}_j) = 0$ | $u$ is the index of a custom constraint.<br> $j$ ranges over the set of rows $\mathsf{CUS}_u$ for which the custom constraint is switched on. |

Here $p_u \typecolon \F^{[m]} \to \F$ is an arbitrary [multivariate polynomial](https://en.wikipedia.org/wiki/Polynomial_ring#Definition_(multivariate_case)):

> Given $\eta$ symbols $X_i$ for $i \typecolon [\eta]$ called indeterminates, a multivariate polynomial $P$ in these indeterminates with coefficients in $\F$ is a finite linear combination
>
> $$P\!\left(\vector{X_b}{b \gets \range{0}{\eta}}\right) = \sum_{z \stypecolon [\nu]} \Big(c_z \cdot \prod_{b \stypecolon [\eta]} X_b^{\alpha_{z,b}}\Big)$$
>
> where $c_z \typecolon \F \where c_z \neq 0\comma$ $\nu \typecolon \N$, and $\alpha_{z,b} \typecolon \N\stop$

#### Lookup constraints

Lookup constraints enforce that some polynomial function of the witness entries on a row are contained in some table.

The sizes of tables are not limited at this layer. A realization of a proving system using Plonkish arithmetization may limit the supported size of tables, possibly depending on $n$, or it may have some way to compile larger tables.

In this specification, we only support fixed lookup tables determined in advance. This could be generalized to support dynamic tables determined by part of the witness matrix.

| Lookup Constraints | Description |
|:------------------ |:----------- |
| $j \in \mathsf{LOOK}_v \implies$ $\vector{q_{v,s}(\vec{w}_j)}{s \gets \range{0}{L_v}} \in \mathsf{TAB}_v$ | $v$ is the index of a lookup table.<br> $j$ ranges over the set of rows $\mathsf{LOOK}_v$ for which the lookup constraint is switched on. |

Here $\vector{q_{v,s} \typecolon \F^{[m]} \to \F}{s \gets \range{0}{L_v}}$ are multivariate polynomials that collectively map the witness entries $\vec{w}_j$ on the lookup row $j \in \mathsf{LOOK}_v$ to a tuple of field elements. This tuple will be constrained to match some row of the table $\mathsf{TAB}_v$.
