Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_case1 : prime_length_spec [84; 77; 115; 89; 74; 70; 69; 116; 115; 103; 99; 101; 104; 117; 113; 84; 106; 112; 68; 102; 109; 118; 78; 97; 82; 108; 115; 75; 79; 84; 104; 105; 115; 105; 86; 98; 110; 90; 73; 111; 97; 104; 101; 100; 111; 120; 121; 108; 111; 111; 112; 104; 84; 110; 104; 105; 115; 116; 104; 97; 116; 111; 110; 105; 115; 116; 103; 46] false.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.