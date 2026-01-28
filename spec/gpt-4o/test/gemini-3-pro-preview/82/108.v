Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_complex : prime_length_spec [
  76; 102; 103; 100; 111; 79; 115; 118; 97; 98; 99; 100; 101; 97; 122; 121; 120; 119; 118; 117; 116; 115; 114; 113; 112; 111; 110; 109; 108; 101; 100; 99; 98; 97; 97; 98; 99; 100; 101; 97; 101; 98; 99; 100; 100; 101; 102; 122; 121; 120; 119; 118; 117; 116; 115; 107; 114; 113; 112; 111; 110; 109; 108; 107; 106; 105; 76; 103; 100; 111; 79; 115; 118; 97; 98; 99; 100; 101; 97; 98; 99; 97; 98; 99; 100; 101; 97; 98; 99; 104; 103; 102; 101; 100; 99; 98; 97; 97; 98; 97; 99; 100; 97; 98; 99; 100; 101; 102; 103; 101; 97; 100; 102; 103; 98; 99; 97; 98; 101; 97; 98; 99
] false.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.