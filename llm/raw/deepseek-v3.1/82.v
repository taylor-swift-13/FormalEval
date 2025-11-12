
Require Import Coq.Init.Prelude.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Definition prime_length_spec (s : string) (result : bool) : Prop :=
  result = is_prime (String.length s).

Definition is_prime (n : nat) : bool :=
  if n <? 2 then
    false
  else
    negb (existsb (fun x => Nat.eqb (n mod x) 0) (seq 2 (Nat.sqrt n - 1))).
