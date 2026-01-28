Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_long : prime_length_spec [100; 99; 97; 122; 121; 120; 119; 118; 117; 112; 90; 116; 115; 114; 113; 112; 111; 110; 109; 108; 107; 105; 104; 103; 102; 101; 100; 99; 98; 97; 100; 101; 97; 98; 97; 98; 99; 100; 101; 102; 99; 100; 100; 109; 101; 102; 101; 103; 97; 102; 103; 97; 98; 99; 100; 101] false.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.