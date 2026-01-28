Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_long : prime_length_spec [113; 77; 115; 89; 74; 70; 69; 116; 115; 103; 99; 101; 104; 117; 113; 84; 107; 114; 80; 120; 66; 76; 87; 106; 112; 68; 102; 109; 118; 78; 97; 82; 108; 75; 79; 105; 86; 98; 97; 110; 116; 105; 101; 100; 105; 115; 101; 115; 97; 116; 97; 98; 108; 105; 115; 104; 109; 101; 110; 116; 105; 115; 109; 110; 110; 90; 73; 111; 97; 84; 104; 105; 84; 104; 101; 113; 117; 105; 99; 107; 98; 114; 111; 119; 110; 102; 111; 120; 106; 117; 109; 112; 115; 111; 118; 101; 114; 116; 104; 101; 108; 97; 122; 121; 100; 111; 103; 84; 104; 101; 113; 117; 116; 104; 101; 105; 99; 107; 98; 114; 111; 119; 110; 102; 111; 120; 106; 117; 109; 112; 115; 111; 118; 101; 114; 116; 104; 101; 108; 97; 122; 121; 100; 111; 103; 84; 104; 101; 113; 117; 105; 99; 107; 98; 114; 111; 119; 110; 102; 111; 120; 84; 110; 104; 105; 115; 116; 104; 97; 116; 104; 101; 116; 104; 101; 117; 105; 99; 107] true.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.