Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_complex : prime_length_spec [112; 114; 105; 109; 101; 46; 112; 113; 114; 115; 116; 117; 115; 118; 119; 120; 120; 121; 108; 111; 112; 112; 105; 115; 46; 116; 121; 122] false.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.