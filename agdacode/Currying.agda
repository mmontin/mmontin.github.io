open import Data.Nat

module Currying where

+3₀ : ℕ → ℕ -- A simple application of _+_
+3₀ x = x + 3

+3₁ : ℕ → ℕ -- Parameters after the whole name
+3₁ x = _+_ x 3

+3₂ : ℕ → ℕ -- Same with currying
+3₂ x = (_+_ x) 3

+3₃ : ℕ → ℕ -- A lambda function
+3₃ = λ x → x + 3 

+3₄ : ℕ → ℕ -- Short syntax for the lambda function
+3₄ = \x → x + 3

+3₅ : ℕ → ℕ -- Instantiation of the second parameter
+3₅ = _+ 3

