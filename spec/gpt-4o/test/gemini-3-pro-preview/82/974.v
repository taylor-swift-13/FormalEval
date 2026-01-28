Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_sentence : prime_length_spec 
  [84; 104; 105; 115; 32; 115; 101; 99; 110; 116; 101; 110; 99; 101; 32; 104; 97; 115; 109; 32; 97; 32; 108; 101; 110; 103; 116; 104; 32; 116; 104; 97; 116; 32; 105; 115; 32; 110; 116; 104; 97; 97; 77; 115; 89; 74; 70; 69; 116; 115; 103; 99; 101; 104; 117; 113; 84; 107; 114; 80; 104; 105; 77; 105; 77; 99; 86; 106; 102; 114; 104; 87; 120; 106; 116; 104; 97; 116; 109; 110; 119; 69; 121; 76; 116; 102; 120; 66; 76; 87; 106; 112; 68; 102; 109; 118; 78; 97; 82; 108; 75; 98; 79; 105; 86; 98; 110; 90; 73; 100; 111; 103; 79; 46; 101; 115; 116; 97; 98; 108; 105; 115; 116; 97; 98; 99; 100; 101; 102; 103; 115; 112; 114; 101; 46; 116; 117; 118; 119; 120; 121; 122; 104; 109; 101; 105; 110; 116; 97; 114; 105; 97; 110; 105; 111; 97; 111; 116; 32; 112; 114; 105; 109; 101; 46] 
  false.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.