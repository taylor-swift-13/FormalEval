Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_new : prime_length_spec [77; 115; 89; 74; 70; 69; 116; 115; 103; 98; 114; 80; 122; 122; 122; 111; 111; 111; 111; 111; 111; 111; 84; 104; 105; 115; 116; 111; 104; 97; 116; 111; 119; 110; 111; 118; 101; 114; 75; 99; 101; 104; 117; 113; 84; 107; 114; 80; 120; 66; 76; 87; 106; 112; 68; 102; 109; 118; 78; 97; 82; 108; 75; 79; 105; 86; 98; 110; 111; 97; 101; 116; 104; 101] false.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.