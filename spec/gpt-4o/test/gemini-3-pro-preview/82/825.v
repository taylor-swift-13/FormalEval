Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_case : prime_length_spec [112; 114; 105; 109; 120; 121; 108; 111; 112; 105; 108; 101; 110; 104; 103; 116; 104; 104; 101; 46; 104; 77; 99; 86; 106; 114; 119; 69; 121; 76; 116; 86; 114; 120; 105; 105; 121; 108; 111; 112; 105; 80; 122; 122; 122; 111; 111; 111; 111; 111; 114; 103; 115; 116; 102; 105; 105] false.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.