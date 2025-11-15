(* """ Return a greatest common divisor of two integers a and b
>>> greatest_common_divisor(3, 5)
1
>>> greatest_common_divisor(25, 15)
5
""" *)

(* Spec(a, b, output) :=

(a mod output = 0) ∧
(b mod output = 0) ∧
(∀ x ∈ ℕ, (a mod x = 0 ∧ b mod x = 0) → x ≤ output) *)

Require Import ZArith.
Open Scope Z_scope.

Definition Spec (a b output : Z) : Prop :=
  (a mod output = 0) /\
  (b mod output = 0) /\
  (forall x : Z, (a mod x = 0) -> (b mod x = 0) -> x > 0 -> x <= output).
