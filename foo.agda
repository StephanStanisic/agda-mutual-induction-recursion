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

u : (x ∷ ξ) P (p[x])
u : Π(x₁ : ξ₁) ⋯ (xₙ : ξ­ₙ). 

Π(A, B) -> Cartesian product between A and B, e.g. a set containing (a, b) forall a∈A, b∈B

(x) T₀(u' (x))
x → T₀(u' (x))
x → T₀ (u' x)
-}


data Bool : Set where
    true : Bool
    false : Bool

record _×_ (A B : Set) : Set where
  constructor ⟨_,_⟩
  field
    fst : A
    snd : B

mutual
    data U₀ : Set where
        π₀ : (u : U₀) → (u' : (x : T₀ u) → U₀) → U₀
    
    T₀ : U₀ → Set
    T₀ (π₀ u u') = T₀ u × (∀ x → T₀ (u' x))


data unit : Set where
  tt : unit

data empty : Set where

¬_ : Set → Set
¬ A = A → empty
    
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
    neqLeft : {n : ℕ} → zero ≠ succ n
    neqRight : {n : ℕ} → succ n ≠ zero
    neqBoth : {n m : ℕ} → n ≠ m → succ n ≠ succ m

foo : DList ℕ (_≠_)
foo = cons 1 nil tt

foo2 : DList ℕ (_≠_)
foo2 = cons 1 foo ⟨ {!   !} , tt ⟩

foo3 : DList ℕ (_≠_)
foo3 = cons 2 foo ⟨ neqBoth neqRight , tt ⟩ 

variable
    n : ℕ

data Vec (A : Set) : ℕ → Set where
    nil : Vec A 0
    cons : A → Vec A n → Vec A (succ n)
