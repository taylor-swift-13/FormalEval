Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_example : prime_length_spec [84; 104; 87; 84; 104; 105; 115; 120; 121; 108; 105; 111; 112; 104; 111; 120; 110; 105; 115; 116; 116; 104; 97; 97; 97; 116; 120; 106; 109; 110; 122; 84; 110; 104; 101; 32; 113; 117; 108; 101; 110; 103; 116; 104; 105; 99; 107; 112; 32; 98; 114; 111; 119; 110; 111; 118; 101; 114; 32; 102; 111; 120; 32; 106; 117; 100; 111; 103; 46; 105; 115] true.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.