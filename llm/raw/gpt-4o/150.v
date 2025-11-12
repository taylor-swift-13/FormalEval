
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.Prime.

Definition is_prime_spec (a : nat) : bool :=
  negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition x_or_y_spec (n x y : nat) (result : nat) : Prop :=
  result = (if is_prime_spec n then x else y).
