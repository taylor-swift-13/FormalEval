Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_complex : prime_length_spec [77; 115; 89; 74; 70; 69; 116; 115; 103; 99; 101; 104; 117; 113; 84; 107; 114; 80; 120; 66; 76; 87; 106; 112; 68; 77; 115; 89; 74; 70; 69; 116; 115; 103; 99; 101; 104; 117; 113; 84; 107; 114; 80; 120; 66; 87; 120; 106; 116; 104; 97; 116; 109; 110; 102; 111; 120; 99; 122; 76; 108; 97; 110; 116; 105; 100; 105; 115; 101; 114; 115; 116; 97; 98; 108; 105; 97; 110; 115; 109; 104; 110; 90; 73; 116; 104; 101; 111; 97; 102; 109; 118; 78; 97; 82; 108; 75; 79; 105; 86; 98; 110; 90; 87; 73; 116; 104; 101; 111; 97] false.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.