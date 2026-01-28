Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_long : prime_length_spec [98; 114; 111; 119; 110; 84; 104; 101; 108; 101; 110; 101; 103; 97; 98; 99; 100; 101; 102; 103; 97; 98; 99; 100; 112; 114; 105; 109; 101; 46; 111; 103; 84; 104; 101; 113; 117; 105; 99; 107; 98; 114; 111; 119; 110; 102; 111; 120; 106; 117; 109; 112; 115; 111; 118; 101; 114; 116; 104; 101; 108; 97; 122; 121; 100; 111; 103; 84; 104; 101; 113; 117; 105; 99; 107; 98; 114; 111; 119; 110; 102; 111; 120; 106; 117; 109; 112; 111; 118; 101; 114; 104; 101; 108; 97; 122; 121; 100; 111; 103; 84; 104; 101; 113; 117; 105; 99; 107; 115; 111; 118; 101; 114; 116; 104; 101; 108; 97; 122; 121; 100; 111; 103; 105; 97; 100; 101; 115; 104; 104; 105; 112; 114; 105; 109; 101; 46; 112; 113; 121; 114; 115; 116; 117; 115; 118; 119; 120; 120; 121; 108; 111; 112; 112; 105; 115; 116; 121; 122; 106; 107; 108; 109; 110; 111; 84; 104; 105; 115; 116; 104] false.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.