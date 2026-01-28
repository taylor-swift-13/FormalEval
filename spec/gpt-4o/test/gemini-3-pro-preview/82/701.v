Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Example test_prime_length_example : prime_length_spec [105; 105; 80; 122; 122; 120; 121; 108; 111; 112; 105; 115; 116; 84; 65; 87; 112; 74; 122; 111; 111; 111; 111; 111; 114; 103] false.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  reflexivity.
Qed.