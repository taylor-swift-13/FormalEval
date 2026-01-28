Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Fixpoint fibfib_aux (n : nat) (a b c : Z) : Z :=
  match n with
  | 0%nat => a
  | S n' => fibfib_aux n' b c (a + b + c)
  end.

Definition fibfib (n : Z) : Z :=
  fibfib_aux (Z.to_nat n) 0 0 1.

Definition problem_63_pre (n : Z) : Prop := True.

Definition problem_63_spec (n : Z) (res : Z) : Prop :=
  res = fibfib n.

Example test_problem_63 : problem_63_spec 55 65720971788709.
Proof.
  unfold problem_63_spec, fibfib.
  vm_compute.
  reflexivity.
Qed.