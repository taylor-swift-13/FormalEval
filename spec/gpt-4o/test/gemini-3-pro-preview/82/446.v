Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_long : prime_length_spec 
  [84; 104; 101; 84; 104; 105; 84; 104; 105; 84; 104; 101; 113; 117; 105; 99; 107; 98; 114; 111; 119; 110; 102; 111; 120; 106; 117; 109; 112; 115; 111; 118; 110; 101; 114; 116; 104; 101; 108; 97; 122; 121; 100; 111; 103;
   84; 104; 101; 113; 117; 116; 104; 101; 105; 99; 107; 98; 114; 111; 119; 110; 102; 111; 120; 106; 117; 109; 112; 115; 111; 118; 101; 114; 116; 104; 101; 108; 97; 122; 121; 100; 111; 103;
   84; 104; 101; 113; 117; 105; 99; 107; 98; 114; 111; 119; 110; 102; 111; 120; 106; 117; 109; 112; 115; 111; 118; 101; 114; 116; 104; 101; 108; 97; 122; 121; 100; 111; 103;
   84; 104; 101; 113; 117; 105; 99; 107; 98; 114; 111; 119; 110; 102; 111; 120; 106; 117; 109; 112; 115; 111; 118; 101; 114; 116; 104; 101; 108; 97; 122; 121; 100; 111; 103;
   84; 104; 101; 113; 117; 105; 99; 107; 98; 114; 111; 119; 110; 102; 111; 120; 117; 109; 112; 115; 111; 118; 101; 114; 116; 104; 101; 108; 97; 122; 121; 100; 111; 103;
   115; 116; 104; 97; 97; 116; 115; 115] false.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.