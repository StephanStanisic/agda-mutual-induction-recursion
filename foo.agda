module foo where

{-
(x : α)β 
Π(x : α). β


(α)β
α → β

x(β)
λx. (N : β)

f(α)
f α

(a ∷ α)β
(a₁ : α₁) ⋯ (aₙ : αₙ)β
Π(a₁ : α₁)(aₙ : αₙ). β
-}

data Bool : Set where
    true : Bool
    false : Bool

record _×_ (A B : Set) : Set where
  constructor ⟨_,_⟩
  field
    fst : A
    snd : B

data unit : Set where
  tt : unit

data empty : Set where
    
module _ (A : Set) (_#_ : A → A → Set) where
    mutual
        data DList : Set where
            nil : DList
            cons : (b : A) → (u : DList) → (P : fresh u b) → DList

        fresh : DList → A → Set
        fresh nil a = unit
        fresh (cons b u P) a = (a # b) × fresh u a

data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data _≠_ : ℕ → ℕ → Set where
    eqfst : {n : ℕ} → zero ≠ succ n
    eqsnd : {n : ℕ} → succ n ≠ zero
    eqboth : {n m : ℕ} → n ≠ m → succ n ≠ succ m

foo : DList ℕ (_≠_)
foo = cons 1 nil tt

foo2 : DList ℕ (_≠_)
foo2 = cons 1 foo ⟨ {!   !} , tt ⟩

foo3 : DList ℕ (_≠_)
foo3 = cons 2 foo ⟨ eqboth eqsnd , tt ⟩