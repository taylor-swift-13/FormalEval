Require Import Coq.Init.Nat.

Fixpoint fibfib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    match n' with
    | 0 => 0
    | S n'' =>
      match n'' with
      | 0 => 1
      | S n''' => fibfib n' + fibfib n'' + fibfib n'''
      end
    end
  end.

Definition problem_63_spec (n : nat) (res : nat) : Prop :=
  res = fibfib n.

Example test_fibfib_15 : problem_63_spec 15 1705.
Proof.
  unfold problem_63_spec.
  simpl.

  (* Evaluate fibfib 15 using the definition, unfolding step by step or using vm_compute *)
  vm_compute.
  reflexivity.
Qed.