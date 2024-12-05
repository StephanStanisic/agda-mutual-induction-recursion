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
    \usepackage{minted}
    \usepackage[overridenote]{pdfpc}
    \newcommand{\talknote}[1]{{\pdfpcnote{- #1}}}
mainfont: Open Sans
mainfontoptions: Scale=0.8
sansfont: Open Sans
sansfontoptions: Scale=0.8
monofont: Fira Code
monofontoptions: Scale=0.8
---

## Contents

* What is simultaneous induction-recursion?
* General schema
* Tarski Universe Construction

# What is simultaneous induction-recursion?

## Induction-Recursion

Basic Idea: Define a function and its domain at the **same** time.

$f: D \to R$

- The function definition is recursive by induction on $D$,
- and the datatype $D$ depends on $f$.

## Motivation

Let's say we are defining a little expression language. 

```coq
Inductive Exp : Set -> Set :=
| add        : Exp nat  -> Exp nat -> Exp nat
| ifthenelse : Exp bool -> Exp nat -> Exp nat -> Exp nat
| lt         : Exp nat  -> Exp nat -> Exp bool.
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
Inductive Exp : Set -> Set :=
| add        : Exp nat  -> Exp nat -> Exp nat
| ifthenelse : Exp bool -> Exp nat -> Exp nat -> Exp nat
| lt         : Exp nat  -> Exp nat -> Exp bool
| printf     : string   -> ?       -> Exp unit.
```

## Generating the type of printf

```coq
Inductive Exp : Set -> Set :=
| add        : Exp nat  -> Exp nat -> Exp nat
| ifthenelse : Exp bool -> Exp nat -> Exp nat -> Exp nat
| lt         : Exp nat  -> Exp nat -> Exp bool
| printf     : forall n : string, printftype n -> Exp unit
with
Fixpoint printftype (s : string) : Set :=
  ?
```

## Generating the type of printf

```coq
Inductive Exp : Set -> Set :=
| add        : Exp nat  -> Exp nat -> Exp nat
| ifthenelse : Exp bool -> Exp nat -> Exp nat -> Exp nat
| lt         : Exp nat  -> Exp nat -> Exp bool
| printf     : forall n : string, printftype n -> Exp unit
with
Fixpoint printftype (s : string) : Set :=
  match s with
  | "%d" ++ xs => prod (Exp nat) (printftype xs)
  ?
  end.
```

## Generating the type of printf

```coq
Inductive Exp : Set -> Set :=
| add        : Exp nat  -> Exp nat -> Exp nat
| ifthenelse : Exp bool -> Exp nat -> Exp nat -> Exp nat
| lt         : Exp nat  -> Exp nat -> Exp bool
| printf     : forall n : string, printftype n -> Exp unit
with
Fixpoint printftype (s : string) : Set :=
  match s with
  | "%d" ++ xs => prod (Exp nat) (printftype xs)
  | String _ xs => printftype xs
  | EmptyString => Exp unit
  end.
```

## Induction-Recursion

```coq
Inductive DList (A : Set) : Set :=
| nil : DList A
| cons : forall (b : A) (u : DList), fresh u b -> DList A
with
Fixpoint fresh (as : DList A) (a : A) : Set :=
  match as with
  | nil => true
  | cons x xs p => x != a /\ fresh xs a
  end.
```

\talknote{Note that we'll have A implicit and != as well in the remainder of the slides.}

<!--- Intuitively: At a certain stage we may have constructed some u: Dlist since fresh is defined by dlist-recursion we already know what it menas for an elem b: S to be fresh wrt u. That is, we know what b' is as a proof. hence, it makes sense to construct cons.
**Note**: Other definition of DList are possible (eg. list with nodup proof). But this definition maybe feels natural and is distinct by construction. --->

# General Schema for Induction-Recursion

## General Schema

- Formation Rules
- Introduction Rules
- Equality Rules
- Elimination Rules

## General Schema : Formation Rules

\talknote{Note: Following the paper, these definitions consider one inductive type and one recursive function. Can be generalised to more}

Formation Rules:

$$
\begin{aligned}
    P &: (A :: \sigma)(a :: \alpha[A])\set \\
    f &: \underbrace{(A :: \sigma)}_{\text{parameters}}\underbrace{(a :: \alpha[A])}_{\text{indices}}(c : P(A,a))\psi[A,a]
\end{aligned}
$$


. . .

\talknote{Here we require that \psi[A,a] is a type under the assumptions A :: \sigma and a :: \alpha[A]}

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
\underbrace{\on{Fresh}}_{f} &: \underbrace{(A : \set)(\neq \; : (A)(A)\set)}_{A}\underbrace{(c : \on{DList} A)}_{c}\underbrace{(a : A)\set}_{\psi[A,a]}
\end{aligned}
$$

\talknote{Here \psi is the type of predicates over elements in the set A under consideration}

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

\talknote{dots here indicate that there may be $0$ or more.} 
\talknote{NOTE: "they may appear in any order".}

---

## General Schema : Introduction Rules

Typing criteria for $\xi, p$ and $q$ are analogous.
$$
\textit{intro} : \;\; \cdots \;\; (b : \beta[\ldots,b',\ldots,u',\ldots]) \;\; \cdots (u : (x :: \xi)P(p[x])) \cdots P(q)
$$
Here $b' : \beta'$ and $u' : (x' :: \xi')P(p'[x'])$ are non-recursive and recursive earlier premises respectively.

Dependence on earlier recursive premise should only happen through application of $f$, that is
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
\textit{intro} : \;\; \cdots \;\;  (b : \beta)\;\;\cdots \;\;(u : (x :: \xi)P(p[x]))\;\; \cdots \;\; P(q)
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

\talknote{At a certain stage we may have constructed u: Dlist. Since Fresh
is defined by Dlist-recursion, we already know what it means for an element b: A to
be fresh with respect to u, that is, we know what a proof b': Fresh(u, b) is. Hence
it makes sense to construct an element cons(b, u, b'). Moreover, we can define
Fresh(cons(b, u, b')) in terms of the already constructed proposition Fresh}

---

## General Schema : Introduction Rules

$$
\textit{intro} : \;\; \cdots \;\; (b : \beta)\;\;\cdots \;\;(u : (x :: \xi)P(p[x]))\;\; \cdots \;\; P(q)
$$

<!-- $$
\hat{\beta}[\ldots, b', \ldots, (x')f(p'[x'],u'(x')),\ldots]
$$ -->

**Note**: Removing the dependence of $\beta,\xi,p$ and $q$ on earlier recursive terms yield the introduction rules we saw in an earlier presentation:

$$\begin{aligned}
intro:  &\; (A :: \sigma) \\
        &\; (b :: \beta[A]) \\
        &\; (u :: \gamma[A,b]) \\
        &\;P_A(p[A,b])
\end{aligned}$$

\talknote{because then f cannot appear in the introduction rules for P.}

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
f(q,\textit{intro}(\ldots, b, \ldots, u,\ldots)) = e(\ldots,b,\ldots,(x)f(p[x],u(x)),\ldots)
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
f(q,\textit{intro}(\ldots, b, \ldots, u,\ldots)) = e(\ldots,b,\ldots,(x)f(p[x],u(x)),\ldots)
$$

\talknote{
f = Fresh
b = non rec. (a:A)
u = recursive (DList)
H = proof

x : a
}

Example:

$$
\begin{aligned}
  \on{Fresh}(\on{nil}, a) &= (a)\top \\
  \on{Fresh}(\on{cons}(b, u, H), a) &= (a)(b \neq a \land \on{Fresh}(u,a))
\end{aligned}
% \begin{aligned}
%   f(\_, \pi_0(b, u)) &= e(b, u) \\
%   e(v, v') &= \Pi(v, v') \\
%   v &= T_0(\_,U_0) \\
%   v' &= (x)T_0(\_,U_0(x))(T_0 u)
% \end{aligned}
$$

## General Schema : Elimination Rules

Let $P,f$ be a simultaneously defined inductive type $P$ with recursive function $f$.

Then we can define a new function $g$
$$
g: (a :: \alpha)(c : P(a))\phi[a,c]
$$
using $P$-recursion.

\talknote{Exactly the same as the function f, but now \phi may depend on c instead of \psi which did not have this}

---

## General Schema : Elimination Rules

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

# Tarski Universe Construction

## Universes

* Russel style Universe:
  
  If $U$ denotes a universe, then a term $t : U$ is a type.

* Tarski style Universe:

  Every universe consists of a set of _codes_ $U$ and a decoding function $T$ (sometimes also denoted as `el`).
  
  Universe is a pair $(U, T)$.

\talknote{(syntactic) distinction between terms (elements of $U$) and types $t$ is lost.}

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

\talknote{T maps elements of U to the associated type.}

\talknote{Universe contains the _codes_ for types rather than the types itself. A type $A$ is not an element of $U$ rather, $\exists u : U$ such that $T(u) = A$.}

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

Restricting ourselves to $\Pi$ and equality-types:
$$
\begin{aligned}
\pi_0 &: (u: U_0)(u': (x : T_0(u)) U_0)U_0 \\
eq_0 &: (U : U_0)(b,b' : T_0(u))U_0
\end{aligned}
$$

---

## $(U_0, T_0)$ Equality rules

$$
\begin{aligned}
T_0(\pi_0(u, u')) &= \Pi(T_0(u), (x)T_0(u'(x))) \\
T_0(eq_0(u,b, b')) &= \on{Eq}(T_0(u), b, b')
\end{aligned}
$$

Remember: 
$$
\begin{aligned}
\pi_0 : (u: U_0)(u': (x : T_0(u)) U_0)U_0
\end{aligned}
$$

. . .

$$ \Pi x : T_0(u) . T_0(u'(x)) $$

---

## Further Universes

Second universe $(U_1, T_1)$.

Analogous to $(U_0,T_0)$, but we now also add $U_0$ formation.

- Formation Rules:
$$\begin{aligned}
U_1 &: \set, \\
T_1 &: (U_1)\set
\end{aligned}$$

- Introduction and Equality Rules:
$$\begin{aligned}
  \pi_1 &: (u: U_1)(u': (x : T_1(u)) U_1)U_1 \\
  T_1(\pi_1(u, u')) &= \Pi(T_1(u), (x)T_1(u'(x))) \\
  &\; \\
  u_{01} &: U_1 \\
  T_1(u_{01}) &= U_0 \\
\end{aligned}$$

## Further Universes

<!--- This t_01 is a constructor for U_1 --->
$$\begin{aligned}
  t_{01} &: U_0(U_1) \\
  T_1(t_{01}(b)) &= T_0(b)
\end{aligned}$$
Repeat for $(U_2,T_2), (U_3, T_3), \ldots$

---

## Internalizing Universe Construction

We can internalize the construction of universes using a *simultaneous inductive-recursive* scheme.

$$
\begin{aligned}
  P = \on{NextU} &: (U: \set)(T: (U)\set)\set, \\
  f = \on{NextT} &: (U: \set)(T: (U)\set)(\on{NextU}(U, T))\set
\end{aligned}
$$

---

## Internalizing Universe Construction

We can internalize the construction of universes using a *simultaneous inductive-recursive* scheme.

$$
\begin{aligned}
  \on{NextU} &: \set, \\
  \on{NextT} &: (\on{NextU})\set
\end{aligned}
$$

Keep in mind, $U : \set$ and $T : (U)\set$ exist implicitly.

\talknote{Dropping the parameters eases the notation quite a bit.}

---

## Internalizing Universe Construction

$$
\begin{aligned}
  \on{NextU} &: \set, \\
  \on{NextT} &: (\on{NextU})\set
\end{aligned}
$$

$$
\begin{aligned}
* &: \on{NextU} \\
\on{NextT}(*) &= U \\
t &: (b : U)\on{NextU} \\
\on{NextT}(t(b)) &= T(b)
\end{aligned}
$$

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

## Conclusion

We showed:

- The basic idea behind simultaneous induction-recursion.
- A schema to construct simultaneous inductive-recursive definitions.
- How to construct universes (and universe hierarchies) using induction-recursion.

## {.standout}

Questions?