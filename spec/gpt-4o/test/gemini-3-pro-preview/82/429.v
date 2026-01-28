Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_new : prime_length_spec [84; 104; 105; 115; 116; 104; 97; 97; 97; 116; 32; 77; 115; 89; 74; 108; 97; 104; 97; 115; 122; 121; 70; 69; 116; 115; 103; 99; 101; 104; 117; 113; 84; 107; 114; 80; 84; 104; 101; 32; 113; 117; 105; 99; 107; 32; 98; 114; 111; 119; 110; 32; 102; 111; 120; 32; 106; 117; 109; 112; 115; 32; 87; 120; 106; 109; 110; 122; 111; 118; 101; 80; 122; 122; 122; 111; 111; 111; 111; 111; 111; 111; 114; 103; 121; 32; 97; 109; 101; 116; 46] false.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.