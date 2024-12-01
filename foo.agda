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

data _≡_ {A : Set} (x : A) : A → Set where
  instance refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

mutual
    data U₀ : Set where
        π₀ : (u : U₀) → (u' : (x : T₀ u) → U₀) → U₀
        eq₀ : (u : U₀) → (b b' : T₀ u) → U₀
    
    T₀ : U₀ → Set
    T₀ (π₀ u u') = (x : T₀ u) → T₀ (u' x)
    T₀ (eq₀ u b b') = _≡_ {T₀ u} b b'

mutual
    data U (n : ℕ) : Set where
        π : (u : U n) → (u' : (x : T n u) → U n) → U n
        eq : (u : U n) → (b b' : T n u) → U n
    
    T : (n : ℕ) → U n → Set
    T n (π u u') = T n u × (∀ x → T n (u' x))
    T n (eq u b b') = b ≡ b'


-- mutual
--     data Uni : Set₁ where
--         Nextu : (U : Set) → (T : U → Set) → Uni
--         Nextt : (U : Set) → (T : U → Set) → Nextu U T → Uni

record ⊤ : Set where
  instance constructor tt
{-# BUILTIN UNIT ⊤ #-}

data ⊥ : Set where

¬_ : Set → Set
¬ A = A → ⊥

module _ {A : Set} (_#_ : A → A → Set) where
    mutual
        data DList : Set where
            nil : DList
            cons : (b : A) → (u : DList) → (P : fresh u b) → DList

        fresh : DList → A → Set
        fresh nil a = ⊤
        fresh (cons b u P) a = (a # b) × fresh u a

data _≠_ : ℕ → ℕ → Set where
    neqLeft : {n : ℕ} → zero ≠ succ n
    neqRight : {n : ℕ} → succ n ≠ zero
    neqBoth : {n m : ℕ} → n ≠ m → succ n ≠ succ m

foo : DList _≠_
foo = cons 1 nil tt

foo-wrong : DList _≠_
foo-wrong = cons 1 foo ⟨ {!   !} , tt ⟩

foo2 : DList _≠_
foo2 = cons 2 foo ⟨ neqBoth neqRight , tt ⟩ 

foo3 : DList _≠_
foo3 = cons 3 foo2 ⟨ neqBoth (neqBoth neqRight) , ⟨ neqBoth neqRight , tt ⟩ ⟩

foo4 : DList _≠_
foo4 = cons 4 foo3 ⟨ neqBoth (neqBoth (neqBoth neqRight)) , ⟨ neqBoth (neqBoth neqRight) , ⟨ neqBoth neqRight , tt ⟩ ⟩ ⟩

foo5 : DList _≠_
foo5 = cons 5 foo4 ⟨ neqBoth (neqBoth (neqBoth (neqBoth neqRight))) ,
  ⟨ neqBoth (neqBoth (neqBoth neqRight)) ,
  ⟨ neqBoth (neqBoth neqRight) , ⟨ neqBoth neqRight , tt ⟩ ⟩ ⟩
  ⟩
