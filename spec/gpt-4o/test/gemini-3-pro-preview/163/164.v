Require Import List.
Require Import Arith.
Require Import Nat.
Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint zseq (start : Z) (len : nat) : list Z :=
  match len with
  | 0%nat => nil
  | S n => start :: zseq (Z.succ start) n
  end.

Definition generate_integers_spec (a b : Z) (evens : list Z) : Prop :=
  let (a, b) := if a <=? b then (a, b) else (b, a) in
  evens = filter (fun i => i mod 2 =? 0) (zseq a (Z.to_nat (Z.min (b + 1) 10 - a))).

Example test_generate_integers : generate_integers_spec 987654321 101 [].
Proof.
  unfold generate_integers_spec.
  vm_compute.
  reflexivity.
Qed.