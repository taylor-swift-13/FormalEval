Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_Methemnz : prime_length_spec [77; 101; 116; 104; 101; 109; 110; 122; 84; 104; 101; 87; 105; 117; 82; 115; 89; 74; 70; 69; 116; 115; 103; 99; 101; 104; 117; 101; 113; 73; 84; 106; 112; 68; 102; 109; 118; 78; 97; 82; 108; 115; 75; 79; 84; 104; 105; 115; 105; 86; 98; 110; 90; 73; 111; 97] false.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.