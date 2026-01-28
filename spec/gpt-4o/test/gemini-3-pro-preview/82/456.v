Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_antiedisesataxylnisntblishmentasrianism : prime_length_spec [97; 110; 116; 105; 101; 100; 105; 115; 101; 115; 97; 116; 97; 120; 121; 108; 110; 105; 115; 110; 116; 98; 108; 105; 115; 104; 109; 101; 110; 116; 97; 115; 114; 105; 97; 110; 105; 115; 109] false.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.