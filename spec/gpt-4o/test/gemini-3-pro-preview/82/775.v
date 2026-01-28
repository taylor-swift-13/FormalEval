Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_long : prime_length_spec 
  [77; 99; 86; 106; 114; 119; 69; 121; 76; 116; 112; 114; 105; 109; 101; 46; 99; 107; 98; 114; 111; 119; 110; 102; 111; 120; 106; 117; 109; 97; 107; 98; 99; 100; 100; 111; 103; 46; 101; 115; 116; 97; 98; 108; 105; 115; 104; 109; 101; 105; 110; 116; 97; 114; 105; 97; 110; 105; 101; 102; 103; 104; 105; 106; 107; 108; 109; 110; 111; 84; 104; 105; 115; 114; 116; 104; 101; 108; 97; 122; 121; 100; 111; 103; 77; 99; 86; 106; 114; 119; 69; 121; 76; 116; 102; 114; 120; 105; 105; 121; 108; 111; 112; 105; 80; 122; 122; 102; 111; 120; 99; 122; 111; 111; 111; 111; 121; 111; 114; 103; 115; 116; 102; 103; 115; 116] 
  false.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.