open import Agda.Builtin.Bool
open import Agda.Builtin.Nat hiding (_+_; _<_)
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.Unit

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data Type : Set where nat bool unit : Type

printf-type : List Char → Set

data Exp : Type → Set where
  _+_ : Exp nat → Exp nat → Exp nat
  if_then_else_ : Exp bool → Exp nat → Exp nat → Exp nat
  #b : Bool → Exp bool
  #n : Nat → Exp nat
  _<_ : Exp nat → Exp nat → Exp bool
  printf : (format : List Char) → printf-type format → Exp unit

printf-type ('%' ∷ 'd' ∷ rest) = Exp nat × printf-type rest
printf-type ('%' ∷ 'b' ∷ rest) = Exp bool × printf-type rest
printf-type (_ ∷ rest) = printf-type rest
printf-type _ = ⊤ 