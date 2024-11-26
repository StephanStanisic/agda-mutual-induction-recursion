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

data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

infix 4 _≡_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

mutual
    data U₀ : Set where
        --↣₀ : (u : U₀) → (u' : U₀) → U₀
        π₀ : (u : U₀) → (u' : (x : T₀ u) → U₀) → U₀
        eq₀ : (u : U₀) → (b b' : T₀ u) → U₀
    
    T₀ : U₀ → Set
    --T₀ (↣₀ c c₁) = {! c → c₁  !}
    T₀ (π₀ u u') = T₀ u × (∀ x → T₀ (u' x))
    T₀ (eq₀ u b b') = b ≡ b' 

mutual
    data U (n : ℕ) : Set where
        π : (u : U n) → (u' : (x : T n u) → U n) → U n
        eq : (u : U n) → (b b' : T n u) → U n
    
    T : (n : ℕ) → U n → Set
    T n (π u u') = T n u × (∀ x → T n (u' x))
    T n (eq u b b') = b ≡ b'

-- mutual
--     data Uni : Set₁ where
--         Nextu : (U : Uni) → (T : U → Uni) → Uni
--         Nextt : (U : Uni) → (T : U → Uni) → Nextu U T → Uni

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