Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_shThisthaat : prime_length_spec [115; 104; 84; 104; 105; 115; 116; 104; 97; 97; 116; 32; 105; 115; 32; 110; 111; 116; 77; 114; 115; 89; 74; 70; 69; 116; 115; 103; 99; 97; 116; 114; 105; 97; 109; 101; 46; 97; 115] false.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.