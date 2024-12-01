---
author: Dick Arends and Stephan Stanisic
title: A general formulation of simultaneous inductive-recursive definitions in type theory
subtitle: Peter Dybjer, 1998
institute: Radboud University
theme: metropolis
aspectratio: 169
header-includes: |
    \newcommand{\set}{\operatorname*{set}}
    \newcommand{\on}[1]{\operatorname*{#1}}
mainfont: Open Sans
mainfontoptions: Scale=0.8
sansfont: Open Sans
sansfontoptions: Scale=0.8
monofont: Fira Code
monofontoptions: Scale=0.8
---

## Contents

* Similtaneous induction-recursion
* General Scheme
* Examples

# The basics


## Induction-Recursion

<!--- Should we also address the fact that when doing a normal inductive definition we need strict positivity
and when doing a normal recursive definition we need structural recusion for guaranteed termination
--->

Basic Idea: Define a function and its domain at the **same** time.

$f: D \to R$

- The function definition is recursive by induction on $D$,
- and the datatype $D$ depends on $f$.


<!--- Why would we want to do this? --->

. . .

Running Example: `DList` (**D**istinct **List**):

```
data DList where
    S    : set
    diff : (S)(S)set
```

---

## Induction-Recursion

Example: `DList` (**D**istinct **List**):

```agda
S    : set
diff : (S)(S)set
```

<!--- Intuitively: At a certain stage we may have constructed some u: Dlist since fresh is defined by dlist-recursion we already know what it menas for an elem b: S to be fresh wrt u. That is, we know what b' is as a proof. hence, it makes sense to construct cons.
**Note**: Other definition of DList are possible (eg. list with nodup proof). But this definition maybe feels natural and is distinct by construction. --->

# General Schema for Induction-Recursion

## General Schema

- Formation Rules
- Introduction Rules
- Equality Rules
- Elimination Rules

## General Schema : Formation Rules

<!-- (Note we can also parametrize, we can show this, but the notation is very long.) -->

Formation Rules:

$$
\begin{aligned}
    P &: (a :: \alpha) \\
    f &: (a :: \alpha)(c : P(a))\psi[a]
\end{aligned}
$$

. . .

$$
\begin{aligned}
\on{DList} &: \set \\
\on{Fresh} &: (c : \on{DList})(a : A)\set
\end{aligned}
$$

---

## General Schema : Formation Rules

<!-- (Note we can also parametrize, we can show this, but the notation is very long.) -->

Formation Rules:

$$
\begin{aligned}
    P &: (a :: \alpha) \\
    f &: (a :: \alpha)(c : P(a))\psi[a]
\end{aligned}
$$

$$
\begin{aligned}
\underbrace{\on{DList}}_{P} &: \set \\
\underbrace{\on{Fresh}}_{f} &: \underbrace{(c : \on{DList})}_{c}\underbrace{(a : A)\set}_{\psi[a]}
\end{aligned}
$$

*Note*: $\alpha$ is the empty sequence.

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

<!--- dots here indicate that there may be $0$ or more. 

NOTE: "they may appear in any order".

Remark: Removing the dependency of $\beta,\xi,p$ and $q$ on previous recursive premises -> recover schema from prev. presentation. --->

---

## General Schema : Introduction Rules

Introduction Rules:

$$
\textit{intro} : \cdots (b : \beta) \cdots (u : (x :: \xi)P(p[x])) \cdots P(q)
$$

. . .

Example:

$$
\on{cons}: (b : A)(u : \on{DList})(b': \on{Fresh}(u,b))\on{DList}
$$

$3$ premises of which only the second one is recursive.

<!--- Very lonnngggg --->
- $b : A$, non-recursive, $\beta = A$.
- $u : \on{DList}$, recursive, $\xi$ empty and $P = \on{DList}$.
- $b' : \on{Fresh}(u,b)$, non-recursive, depends on $u$ (a $\on{DList}$ instance, but only through the $\on{Fresh}$ function), $\beta[b,u] = \on{Fresh}(u,b)$. 

<!--- 

I think adding the example for pi0 is also nice as it demonstrates a case where u' is generalised and depends on the previous premise.

--->

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

<!--- Not complete yet --->

---

## General Schema: Equality Rules

$$
f(q,\textit{intro}(\ldots, b, \ldots, u,\ldots)) = e(\ldots,b,\ldots,(x)f(p[x],u(x)),\ldots) : \psi[q]
$$
in the context
$$
(\ldots,b: \beta, \ldots,u:(x::\xi)P(p[x]),\ldots)
$$
where 
$$
e(\ldots,b, \ldots, v,\ldots) : \psi[q]
$$
in the context
$$
(\ldots, b : \beta,\ldots, v:(x :: \xi )\psi[p[x]],\ldots)
$$

## General Schema : Elimination Rules

Example: Length of DList;

<!--- Dick: In general we should introduce some notation at the start of the presentation to make sure that everyone know what we are talking about when saying things like P and f --->
Assuming $P$ (inductive type) and $f$ (recursive function), may define 

$$
f': (a :: \alpha)(c : P(a))\psi'[a,c]
$$

<!--- \psi depends on a and c --->
using $P$-recursion.

---

## General Schema: Elimination Rules

Elimination:
$$
f'(q,\textit{intro}(\ldots,b,\ldots,u,\ldots)) = e'(\ldots,b,\ldots, u, (x)f'(p[x], u(x)), \ldots)
$$
in the context
$$
(\ldots,b: \beta, \ldots,u:(x::\xi)P(p[x]),\ldots)
$$
where 
$$
e'(\ldots,b, \ldots, u,v,\ldots) : \psi'[q,\textit{intro}(\ldots,b,\ldots,u,\ldots)]
$$
in the context
$$
(\ldots, b : \beta,\ldots, u:(x :: \xi )P(p[x]), v: (x :: \xi)\psi'[p[x], u(x)],\ldots)
$$

## Example:

```
length: (l : DList)ℕ

```


# Tarski Universe Construction

## Universes

Russel style Universe, this is what we have seen during the Type Theory lectures. 

If $U$ denotes a universe, then a term $t : U$ is a type.

(syntactic) distinction between terms (elements of $U$) and types $t$ is lost.

---

## Tarski Universe

Maintains distinction.

How? Every universe consists of a set of _codes_ $U$ and a decoding function $T$ (sometimes also denoted with `el`).

<!--- T maps elements of U to the associated type.

Universe contains the _codes_ for types rather than the types itself. A type $A$ is not an element of $U$ rather, $\exists u : U$ such that $T(u) = A$. --->

---

## Definition of $U_0$

Goal: Use our induction-recursion framework to construct the first Tarski universe $(U_0, T_0)$.

We need

- Formation rules
- Introduction rules
- Equality rules

---

## $U_0$ Formation rules

$$
\begin{aligned}
U_0 &: \set, \\
T_0 &: (c: U_0)\set
\end{aligned}
$$

<!--- Include general schema to see how it is instantiated in this case. --->

---

## $(U_0, T_0)$ Introduction rules

We would have a constructor (introduction rule) for every type former in the theory.

Restricting ourselves to $\Pi$-types:
$$
\begin{aligned}
\pi_0 : (u: U_0)(u': (x : T_0(u)) U_0)U_0
\end{aligned}
$$

---

## $(U_0, T_0)$ Equality rules

Reminder: 

$$
\begin{aligned}
\pi_0 : (u: U_0)(u': (x : T_0(u)) U_0)U_0
\end{aligned}
$$

$$
\begin{aligned}
T_0(\pi_0(u, u')) = \Pi(T_0(u), (x)T_0(u'(x)))
\end{aligned}
$$

<!--- ie. $T_0$ on $\pi_0(u, u')$ returns the dependent function types from $T_0(u)$ to $T_0(u')$ where $u'$ depends on $x : T_0(u)$.

$$
\Pi\;x:A,B(x)
$$ --->

---

## Further universes

Second universe ($U_1$).

- Formation Rules:
$$\begin{aligned}
U_1 &: \set, \\
T_1 &: (U_1)\set
\end{aligned}$$

. . .

- Introduction Rules:

where we now also add $U_0$ formation.

. . .

Test

---

## Internalizing Universe Construction

We can internalize the construction of universes using a *similtaneous inductive-recursive* scheme.

$$
\begin{aligned}
    \operatorname*{NextU} &: (U: \set)(T: (U)\set)\set, \\
    \operatorname*{NextT} &: (U: \set)(T: (U)\set)(\operatorname*{NextU}(U, T))\set
\end{aligned}
$$

<!--- Dropping the parameters eases the notation quite a bit. --->

---

## Palmgren's Constructions

See 
Palmgren, E. (1991). Fixed point operators, inductive definitions and universes in Martin-Lof’s type theory (on). Uppsala University; Depart. of Mathematics.

## Super Universes

Super universe $U_{\infty}$ is the closure of the universe next universe operator **and** all other type formers.

Formation Rules:
$$
\begin{aligned}
U_{\infty} &: \set \\
T_{\infty} &: (U_{\infty})\set
\end{aligned}
$$

*Note*: Construction looks very much like the first universe construction.

--- 

## Super Universe

$$ u_0 : U_{\infty}, $$
$$ T_{\infty}(u_0) = U_0, $$
$$ \operatorname*{NextU} : (u : U_{\infty})(u' : (T_{\infty}(u))U_{\infty})U_{\infty}, $$
$$ T_{\infty}(\operatorname*{NextU}(u, u')) = \operatorname*{NextU}(T_{\infty}(u), (x)T_{\infty}(u'(x))) $$
