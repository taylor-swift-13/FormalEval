Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_MsYJFEtcsgcehuqTkrPhiiMcVjrwEyLtfItheoa : prime_length_spec [77; 115; 89; 74; 70; 69; 116; 99; 115; 103; 99; 101; 104; 117; 113; 84; 107; 114; 80; 104; 105; 105; 77; 99; 86; 106; 114; 119; 69; 121; 76; 116; 102; 73; 116; 104; 101; 111; 97] false.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.