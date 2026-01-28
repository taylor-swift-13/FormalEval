Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_long_string : prime_length_spec [108; 101; 110; 103; 116; 84; 104; 105; 77; 115; 89; 74; 70; 69; 116; 115; 103; 99; 101; 104; 117; 113; 84; 100; 111; 103; 46; 116; 104; 101; 110; 111; 116; 84; 104; 105; 115; 116; 104; 97; 116; 107; 114; 80; 100; 111; 103; 46; 120; 66; 97; 110; 116; 105; 100; 105; 115; 101; 115; 116; 97; 98; 108; 105; 115; 104; 109; 101; 110; 116; 115; 97; 114; 82; 108; 75; 79; 105; 86; 103; 98; 110; 90; 73; 111; 97; 101; 116; 104; 101; 120; 66; 76; 84; 104; 87; 120; 106; 109; 110; 122; 109; 112; 115; 84; 104; 101] true.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.