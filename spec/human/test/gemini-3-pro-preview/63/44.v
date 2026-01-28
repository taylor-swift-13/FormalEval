Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.

Fixpoint fibfib_aux (n : nat) (a b c : Z) : Z :=
  match n with
  | 0 => a
  | S n' => fibfib_aux n' b c (Z.add (Z.add a b) c)
  end.

Definition fibfib (n : nat) : Z :=
  fibfib_aux n 0%Z 0%Z 1%Z.

Definition problem_63_pre (n : nat) : Prop := True.

Definition problem_63_spec (n : nat) (res : Z) : Prop :=
  res = fibfib n.

Example test_problem_63 : problem_63_spec 49 1697490356184%Z.
Proof.
  unfold problem_63_spec.
  unfold fibfib.
  vm_compute.
  reflexivity.
Qed.