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

* What is similtaneous induction-recursion?
* General schema
* Examples

# The basics


## Induction-Recursion

Basic Idea: Define a function and its domain at the **same** time.

$f: D \to R$

- The function definition is recursive by induction on $D$,
- and the datatype $D$ depends on $f$.

<!-- . . . 

Running Example: `DList` (**D**istinct **List**):

```
data DList where
    S    : set
    diff : (S)(S)set
``` -->

## Motivation

Let's say we are defining a little expression language. 

```coq
Inductive Typ : Set :=
| t_nat
| t_bool
| t_unit.

Inductive Exp : Typ -> Set :=
| intro_bool : bool -> Exp t_bool
| intro_nat  : nat -> Exp t_nat
| ifthenelse : Exp t_bool -> Exp t_nat -> Exp t_nat -> Exp t_nat
| lt         : Exp t_nat  -> Exp t_nat -> Exp t_bool.
```

## printf

Now we would like to add `printf` as a function that is callable from our little expression language. `printf` is a popular function from C for formatting strings:

```c
printf("Welcome, %s!\n", "Ulf Norell");
printf("%s, %s!\n",      "Hello", "Catarina Coquand");
printf("%s (%s, %d)\n",  "Data types à la carte", "Swierstra", 2008);
```

```
Welcome, Ulf Norell!
Hello, Catarina Coquand!
Data types à la carte (Swierstra, 2008)
```

## Updating our language

So we add printf in our expression type, but what do we put into the hole?

```coq
Inductive Typ : Set :=
| t_nat
| t_bool
| t_unit.

Inductive Exp : Typ -> Set :=
| intro_bool : bool -> Exp t_bool
| intro_nat  : nat -> Exp t_nat
| ifthenelse : Exp t_bool -> Exp t_nat -> Exp t_nat -> Exp t_nat
| lt         : Exp t_nat  -> Exp t_nat -> Exp t_bool
| printf     : Exp t_str  -> ?         -> Exp t_unit.
```

## Generating the type of printf

```coq
Inductive Exp : Set -> Set :=
| add        : Exp nat  -> Exp nat -> Exp nat
| ifthenelse : Exp bool -> Exp nat -> Exp nat -> Exp nat
| lt         : Exp nat  -> Exp nat -> Exp bool
| printf     : (n : string) -> printftype n -> Exp unit
where
Fixpoint printftype (s : string) : Exp :=
  match s with
  | "%d" ++ xs => prod (Exp nat) (printftype xs)
  | "%b" ++ xs => prod (Exp bool) (printftype xs)
  | String _ xs => printftype xs
  | _ => Exp unit
  end.
```

---

## Induction-Recursion

Example: $\on{DList}$ (**D**istinct **List**):

$$
\begin{aligned}
A &: \set \\
\neq &: (A)(A)\set
\end{aligned}
$$



<!--- Intuitively: At a certain stage we may have constructed some u: Dlist since fresh is defined by dlist-recursion we already know what it menas for an elem b: S to be fresh wrt u. That is, we know what b' is as a proof. hence, it makes sense to construct cons.
**Note**: Other definition of DList are possible (eg. list with nodup proof). But this definition maybe feels natural and is distinct by construction. --->

# General Schema for Induction-Recursion

## General Schema

- Formation Rules
- Introduction Rules
- Equality Rules
- Elimination Rules

## General Schema : Formation Rules

<!--- Note: Following the paper, these definitions consider one inductive type and one recursive function. Can be generalised to more --->

Formation Rules:

$$
\begin{aligned}
    P &: (A :: \sigma)(a :: \alpha[A])\set \\
    f &: \underbrace{(A :: \sigma)}_{\text{parameters}}\underbrace{(a :: \alpha[A])}_{\text{indices}}(c : P(A,a))\psi[A,a]
\end{aligned}
$$

<!--- Here we require that \psi[A,a] is a type under the assumptions A :: \sigma and a :: \alpha[A] --->

. . .

$$
\begin{aligned}
\on{DList} &: (A : \set)(\neq \; : (A)(A)\set)\set \\
\on{Fresh} &: (A : \set)(\neq \; : (A)(A)\set)(c : \on{DList})(a : A)\set
\end{aligned}
$$

---

## General Schema : Formation Rules

Formation Rules:

$$
\begin{aligned}
    P &: (A :: \sigma)(a :: \alpha[A])\set \\
    f &: (A :: \sigma)(a :: \alpha[A])(c : P(A,a))\psi[A,a]
\end{aligned}
$$

$$
\begin{aligned}
\underbrace{\on{DList}}_{P} &: \underbrace{(A : \set)(\neq \; : (A)(A)\set)}_{A}\set \\
\underbrace{\on{Fresh}}_{f} &: \underbrace{(A : \set)(\neq \; : (A)(A)\set)}_{A}\underbrace{(c : \on{DList})}_{c}\underbrace{(a : A)\set}_{\psi[A,a]}
\end{aligned}
$$

<!-- Here \psi is the type of predicates over elements in the set A under consideration -->

*Note*: $\alpha[A]$ is the empty sequence.

---

## General Schema : Formation Rules

The previous slide showed explicit parameters, in the rest of the presentation we consider parameters to be implicit.

Resulting in:

$$
\begin{aligned}
    P &: (a :: \alpha)\set \\
    f &: (a :: \alpha)(c : P(a))\psi[a]
\end{aligned}
$$

---

## General Schema : Introduction Rules

Introduction Rules:

$$
\textit{intro} : \;\; \cdots \;\; (b : \beta)\;\; \cdots \;\; (u : (x :: \xi)P(p[x])) \;\; \cdots \;\; P(q)
$$

## General Schema : Introduction Rules

Introduction Rules:

$$
\textit{intro} : \;\; \cdots \;\; \underbrace{(b : \beta)}_{\text{non-recursive}} \;\; \cdots \;\; \underbrace{(u : (x :: \xi)P(p[x]))}_{\text{recursive}} \;\; \cdots \;\; P(q)
$$

<!--- dots here indicate that there may be $0$ or more. 

NOTE: "they may appear in any order". --->

---

## General Schema : Introduction Rules

Typing criteria for $\xi, p$ and $q$ are analogous.
$$
\textit{intro} : \;\; \cdots \;\; (b : \beta[\ldots,b',\ldots,u',\ldots]) \;\; \cdots (u : (x :: \xi)P(p[x])) \cdots P(q)
$$
Here $b' : \beta'$ and $u' : (x' :: \xi')P(p'[x'])$ are non-recursive and recursive earlier premises respectively.

Dependence on earlier recursive premise can only happen through application of $f$, that is
$$
\beta[\ldots,b',\ldots,u',\ldots]
$$
must be of the form
$$
\hat{\beta}[\ldots, b', \ldots, (x')f(p'[x'],u'(x')),\ldots]
$$

<!-- (x')f(p'[x'],u'(x')) is an abstraction?  -->

---

## General Schema : Introduction Rules

$$
\textit{intro} : \cdots (b : \beta)\cdots \;\;(u : (x :: \xi)P(p[x]))\;\; \cdots \;\; P(q)
$$

where
$$
\hat{\beta}[\ldots, b', \ldots, (x')f(p'[x'],u'(x')),\ldots]
$$
is a small type in the context
$$
(\ldots, b':\beta',\ldots, v' : (x' :: \xi')\psi[p'[x']], \ldots)
$$

---

## General Schema : Introduction Rules

$$
\textit{intro} : \cdots (b : \beta)\cdots \;\;(u : (x :: \xi)P(p[x]))\;\; \cdots \;\; P(q)
$$

$$
\hat{\beta}[\ldots, b', \ldots, (x')f(p'[x'],u'(x')),\ldots]
$$

**Note**: Removing the dependence of $\beta,\xi,p$ and $q$ on earlier recursive terms yield the introduction rules we saw in an earlier presentation:

$$\begin{aligned}
intro:  &\; (A :: \sigma) \\
        &\; (b :: \beta[A]) \\
        &\; (u :: \gamma[A,b]) \\
        &\;P_A(p[A,b])
\end{aligned}$$

<!--- Until here we should write the introduction rules with \beta explicitly --->

---

## General Schema : Introduction Rules

Introduction Rules:
$$
\textit{intro} : \cdots (b : \beta) \cdots (u : (x :: \xi)P(p[x])) \cdots P(q)
$$

Example:
$$
\begin{aligned}
\on{nil}  &: \on{DList} \\
\on{cons} &: (b : A)(u : \on{DList})(H: \on{Fresh}(u,b))\on{DList}
\end{aligned}
$$

$3$ premises of which only the second one is recursive.

<!--- Very lonnngggg --->
- $b : A$, non-recursive, $\beta = A$.
- $u : \on{DList}$, recursive, $\xi$ empty and $P = \on{DList}$.
- $H : \on{Fresh}(u,b)$, non-recursive, depends on $u$ (a $\on{DList}$ instance, but only through $\on{Fresh}$), $\beta[b,u] = \hat{\beta}[b, \on{Fresh}(u)] = \on{Fresh}(u,b)$. 

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

## General Schema : Equality Rules

$$
f(q,\textit{intro}(\ldots, b, \ldots, u,\ldots)) = e(\ldots,b,\ldots,(x)f(p[x],u(x)),\ldots) : \psi[q]
$$

Example:

$$
\begin{aligned}
  \on{Fresh}(\on{nil}, a) &= (a)\top \\
  \on{Fresh}(\on{cons}(b, u, H), a) &= (a)(b \neq a \land \on{Fresh}(u,a))
\end{aligned}
$$

## General Schema : Elimination Rules

Let $P,f$ be a similtaneously defined inductive type $P$ with recursive function $f$.

Then we can define a new function $g$
$$
g: (a :: \alpha)(c : P(a))\phi[a,c]
$$
using $P$-recursion.

<!--- Exactly the same as the function f, but now \phi may depend on c instead of \psi which did not have this --->

---

## General Schema: Elimination Rules

Elimination:
$$
g(q,\textit{intro}(\ldots,b,\ldots,u,\ldots)) = e'(\ldots,b,\ldots, u, (x)g(p[x], u(x)), \ldots)
$$
in the context
$$
(\ldots,b: \beta, \ldots,u:(x::\xi)P(p[x]),\ldots)
$$
where 
$$
e'(\ldots,b, \ldots, u,v,\ldots) : \phi[q,\textit{intro}(\ldots,b,\ldots,u,\ldots)]
$$
in the context
$$
(\ldots, b : \beta,\ldots, u:(x :: \xi )P(p[x]), v: (x :: \xi)\phi[p[x], u(x)],\ldots)
$$

## General Schema : Elimination Rules

Example:
$$
\begin{aligned}
  \on{length} &: (c : \on{DList})\mathbb{N} \\
  \on{length}(\on{nil}) &= 0 \\
  \on{length}(\on{cons(b, u, H)}) &= S(\on{length}(u))
\end{aligned}
$$

<!--- Typing rule for length --->

# Tarski Universe Construction

## Universes

* Russel style Universe:
  
  If $U$ denotes a universe, then a term $t : U$ is a type.

* Tarski style Universe:

  Every universe consists of a set of _codes_ $U$ and a decoding function $T$ (sometimes also denoted as `el`).
  
  Universe is a pair $(U, T)$.

<!-- (syntactic) distinction between terms (elements of $U$) and types $t$ is lost. -->

---

## Tarski Universe

Example: Universe $(U,T)$ containing types for natural numbers and boolean values:

$$
\begin{aligned}
  \langle\textit{naturals}\rangle &: U \\
  \langle\textit{booleans}\rangle &: U \\
  T(\langle\textit{naturals}\rangle) &= \mathbb{N} \\
  T(\langle\textit{booleans}\rangle) &= \mathbb{B} \\
  3 &: \mathbb{N} \\
  \on{True} &: \mathbb{B}
\end{aligned}
$$

<!--- T maps elements of U to the associated type.

Universe contains the _codes_ for types rather than the types itself. A type $A$ is not an element of $U$ rather, $\exists u : U$ such that $T(u) = A$. --->

---

## Definition of $(U_0, T_0)$

Goal: Use our induction-recursion framework to construct the first Tarski universe $(U_0, T_0)$.

We need

- Formation rules
- Introduction rules
- Equality rules

---

## $(U_0, T_0)$ Formation rules

$$
\begin{aligned}
U_0 &: \set, \\
T_0 &: (c: U_0)\set
\end{aligned}
$$

<!--- Include general schema to see how it is instantiated in this case. --->

---

## $(U_0, T_0)$ Introduction rules

We need a constructor (introduction rule) for every type former in the theory.

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

Second universe $U_1$.

- Formation Rules:
$$\begin{aligned}
U_1 &: \set, \\
T_1 &: (U_1)\set
\end{aligned}$$

. . .

- Introduction Rules:

  Similar as for $(U_0,T_0)$, but we now also add $U_0$ formation.
$$\begin{aligned}
  u_{01} &: U_1 \\
  T_1(u_{01}) &= U_0 \\
  T_1(\pi_1(u, u')) &= \Pi(T_1(u), (x)T_1(u'(x))) \\
  t_{01} &: U_0(U_1) \\
  T_1(t_{01}(b)) &= T_0(b)
\end{aligned}$$
Repeat for $(U_2,T_2), (U_3, T_3), \ldots$

<!--- This t_01 is a constructor for U_1 --->

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

<!-- ## Palmgren's Constructions

See 
Palmgren, E. (1991). Fixed point operators, inductive definitions and universes in Martin-Lof’s type theory (on). Uppsala University; Depart. of Mathematics. -->

---

## Super Universes

Super universe $U_{\infty}$ is the closure of the next universe operator **and** all other type formers.

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

## {.standout}

Questions?