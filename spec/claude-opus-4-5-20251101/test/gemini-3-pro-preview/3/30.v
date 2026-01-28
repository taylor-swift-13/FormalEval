Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Fixpoint prefix_sums (ops : list Z) (acc : Z) : list Z :=
  match ops with
  | [] => []
  | op :: rest => let new_acc := acc + op in new_acc :: prefix_sums rest new_acc
  end.

Definition below_zero_spec (operations : list Z) (result : bool) : Prop :=
  let balances := prefix_sums operations 0 in
  result = true <-> exists bal, In bal balances /\ bal < 0.

Example test_case_1 : below_zero_spec [0; 35] false.
Proof.
  unfold below_zero_spec.
  simpl.
  split.
  - intro H.
    discriminate H.
  - intro H.
    destruct H as [bal [H_in H_lt]].
    destruct H_in as [H_eq | [H_eq | H_absurd]].
    + subst bal.
      inversion H_lt.
    + subst bal.
      inversion H_lt.
    + inversion H_absurd.
Qed.