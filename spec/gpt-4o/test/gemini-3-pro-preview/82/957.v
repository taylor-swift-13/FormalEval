Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_long : prime_length_spec [84; 104; 101; 32; 113; 117; 105; 99; 107; 32; 98; 114; 111; 119; 110; 101; 32; 102; 111; 120; 32; 106; 117; 109; 112; 115; 32; 111; 118; 101; 114; 32; 116; 104; 101; 32; 108; 100; 111; 103; 46; 104; 97; 112; 114; 105; 109; 101; 46; 112; 114; 113; 114; 115; 116; 114; 117; 118; 119; 120; 121; 122; 115; 97; 122; 121; 32; 100; 111; 103; 108; 101; 110; 101; 103; 116; 120; 68; 115; 104; 46] false.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.