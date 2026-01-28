Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_brown : prime_length_spec [98; 114; 111; 119; 110; 84; 87; 120; 106; 116; 104; 97; 116; 109; 110; 102; 111; 120; 99; 111; 122; 104; 113; 117; 105; 99; 107; 97; 110; 116; 105; 100; 105; 115; 84; 104; 101; 101] false.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.