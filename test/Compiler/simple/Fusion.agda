{-# OPTIONS --rewriting #-}

module Fusion where

open import Agda.Builtin.List

variable A B C : Set

map : (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

open import Agda.Builtin.Equality

cong : ∀ (f : A → B) {a b} → a ≡ b → f a ≡ f b
cong f refl = refl

map-fusion : ∀ (g : B → C) (f : A → B) xs →
             map g (map f xs) ≡ map (λ x → g (f x)) xs
map-fusion g f [] = refl
map-fusion g f (x ∷ xs) = cong (g (f x) ∷_) (map-fusion g f xs)

id : A → A
id a = a

map-id : (xs : List A) → map id xs ≡ xs
map-id [] = refl
map-id (x ∷ xs) = cong (x ∷_) (map-id xs)

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE map-fusion map-id #-}

open import Agda.Builtin.Nat

inc2 : List Nat → List Nat
inc2 xs = map (1 +_) (map (1 +_) xs) -- reduced to map (2 +_) xs

id2 : List (List A) → List (List A)
id2 xs = map (map id) xs -- reduced to xs

plus : Nat → Nat → Nat
plus zero n = n
plus (suc m) n = plus m (suc n)

+-suc : ∀ m n → m + suc n ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n = cong suc (+-suc m n)

plus-correct : ∀ m n → plus m n ≡ m + n
plus-correct zero n = refl
plus-correct (suc m) n
  rewrite plus-correct m (suc n)
  | +-suc m n = refl

{-# REWRITE plus-correct #-}

map+ : Nat → List Nat → List Nat
map+ k = map (plus k) -- does not fire because we're lacking eta-expansion

map+' : Nat → List Nat → List Nat
map+' k = map (λ l → plus k l) -- does not fire because Agda eta-contracts the function

map+'' : Nat → List Nat → List Nat
map+'' k = map (λ l → plus l k) -- fires just fine
