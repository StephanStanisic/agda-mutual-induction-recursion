---
author: Dick Arends and Stephan Stanisic
title: A general formulation of simultaneous inductive-recursive definitions in type theory
subtitle: Peter Dybjer, 1998
institute: Radboud University
theme: metropolis
aspectratio: 169
---

## Contents

Here is an example

* Similtaneous induction-recursion
* General Scheme
* Examples

# The basics


## Induction-Recursion

Basic Idea: Define a function $f: D \to R$ and its domain of definition $D$ at the **same** time, $D$ may use $f$.

Why would we want to do this?

. . .

Running Example: `DList` (**D**istinct **List**):

```
S    : set
diff : (S)(S)set
```

---

## Induction-Recursion

Example: `DList` (**D**istinct **List**):

```
S    : set
diff : (S)(S)set
```

Intuitively: At a certain stage we may have constructed some u: Dlist since fresh is defined by dlist-recursion we already know what it menas for an elem b: S to be fresh wrt u. That is, we know what b' is as a proof. hence, it makes sense to construct cons.

Note: Other definition of DList are possible (eg. list with no dup proof). But this definition maybe feels natural and is distinct by construction.

---

# General Schema for Induction-Recursion

## General Schema

What do we need?

- Formation Rules
- Introduction Rules
- Equality Rules

## General Schema : Formation Rules

(Note we can also parametrize)

Formation Rules:

$$
\begin{aligned}
    P &: (a :: \alpha) \\
    f &: (a :: \alpha)(c : P(\alpha))\psi[\alpha]
\end{aligned}
$$

Example!

---

## General Schema : Introduction Rules

Introduction Rules:

$$
\textit{intro} : \cdots (b : \beta) \cdots (u : (x :: \xi)P(p[x])) \cdots P(q)
$$

---

## General Schema : Introduction Rules

Introduction Rules:

$$
\textit{intro} : \cdots \underbrace{(b : \beta)}_{\text{non-recursive}} \cdots \;\; \underbrace{(u : (x :: \xi)P(p[x]))}_{\text{recursive}} \;\; \cdots \;\; P(q)
$$

dots here indicate that there may be $0$ or more. 

NOTE: "they may appear in any order".

Remark: Removing the dependency of $\beta,\xi,p$ and $q$ on previous recursive premises -> recover schema from prev. presentation. 

---

## General Schema : Equality Rules

Equality Rules:

$$
f(q,\textit{intro}(\ldots, b, \ldots, u,\ldots)) = e(\ldots,b,\ldots,(x)f(p[x],u(x)),\ldots) : \psi[q]
$$

Reminder: 
$$
\textit{intro} : \cdots \underbrace{(b : \beta)}_{\text{non-recursive}} \cdots \;\; \underbrace{(u : (x :: \xi)P(p[x]))}_{\text{recursive}} \;\; \cdots \;\; P(q)
$$

---

# Tarski Universe Construction

## Universes

Russel style Universe, this is what we have seen during the Type Theory lectures. 

If $U$ denotes a universe, then a term $t : U$ is a type.

(syntactic) distinction between terms (elements of $U$) and types $t$ is lost.

---

## Tarski Universe

Maintains distinction.

How? Every universe consists of a set of _codes_ $U$ and a decoding function $T$ (sometimes also denoted with `el`).

T maps elements of U to the associated type.

Universe contains the _codes_ for types rather than the types itself. A type $A$ is not an element of $U$ rather, $\exists u : U$ such that $T(u) = A$.

---

## Palmgren's Constructions

See 
Palmgren, E. (1991). Fixed point operators, inductive definitions and universes in Martin-Lof’s type theory (on). Uppsala University; Depart. of Mathematics.
