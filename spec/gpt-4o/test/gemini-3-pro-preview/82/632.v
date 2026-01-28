Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Definition chunk : list nat := 
  [84; 104; 101; 113; 117; 105; 99; 107; 98; 114; 111; 119; 110; 102; 111; 120; 106; 117; 109; 112; 115; 111; 118; 101; 114; 116; 104; 101; 108; 97; 122; 121; 100; 111; 103].

Definition suffix : list nat := 
  [84; 104; 101; 113; 117; 105; 99; 107; 115; 111; 118; 101; 114; 116; 104; 101; 108; 97; 122; 121; 100; 111; 103; 115; 101; 110; 116; 101; 110; 99; 101].

Definition input_str := chunk ++ chunk ++ chunk ++ chunk ++ suffix.

Example test_prime_length_long : prime_length_spec input_str false.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  unfold input_str, chunk, suffix.
  simpl.
  reflexivity.
Qed.