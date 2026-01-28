Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_new : prime_length_spec [77; 99; 86; 106; 114; 119; 102; 69; 121; 87; 122; 120; 106; 84; 104; 87; 84; 104; 105; 115; 116; 104; 97; 97; 97; 116; 120; 106; 109; 110; 122; 84; 104; 101; 32; 113; 117; 108; 101; 110; 103; 116; 104; 105; 99; 107; 112; 32; 98; 114; 111; 119; 110; 111; 118; 101; 114; 32; 102; 111; 120; 32; 106; 117; 100; 77; 115; 89; 74; 70; 69; 116; 115; 103; 99; 101; 104; 117; 113; 84; 107; 114; 80; 120; 66; 76; 87; 106; 112; 68; 102; 109; 118; 78; 104; 97; 82; 108; 75; 79; 105; 86; 98; 110; 90; 73; 111; 97; 111; 103; 46; 105; 115; 109; 110; 122; 76; 116; 102] false.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.