Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Import ListNotations.

Definition is_prime_spec (a : nat) (result : bool) : Prop :=
  result = negb (orb (a <? 2) (existsb (fun x => a mod x =? 0) (seq 2 (Nat.sqrt a - 1)))).

Definition prime_length_spec (string : list nat) (result : bool) : Prop :=
  is_prime_spec (length string) result.

Definition Hello : list nat := [72; 101; 108; 108; 111].

Example test_case_Hello : prime_length_spec Hello true.
Proof.
  unfold prime_length_spec.
  unfold is_prime_spec.
  simpl.
  vm_compute.
  reflexivity.
Qed.