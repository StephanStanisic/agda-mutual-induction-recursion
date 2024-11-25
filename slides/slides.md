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

Basic Idea: Define a function $f: D \to R$ and its domain of definition $D$ at the **same** time.

Why would we want to do this?

. . .

Example: `DList` (**D**istinct **List**):

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
\textit{intro} : \cdots \underbrace{(b : \beta)}_{\text{non-recursive}} \cdots \;\; \underbrace{(u : (x :: \xi)P(p[x]))}_{\text{recursive}} \;\; \cdots P(q)
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
\textit{intro} : \cdots \underbrace{(b : \beta)}_{\text{non-recursive}} \cdots \;\; \underbrace{(u : (x :: \xi)P(p[x]))}_{\text{recursive}} \;\; \cdots P(q)
$$

---

## What about code?

We can even have code...

```haskell
data List a = Nil | Cons a (List a)
```

with (some) syntax highlighting


# How about a new section?

---

## Alerts? Bold?

We can have **bold text**

We can also have \alert{alerted text} if you must

---

## {.standout}

Questions?
