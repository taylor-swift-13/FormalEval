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

Example test_case_1 : below_zero_spec [30%Z; -3%Z; -15%Z] false.
Proof.
  unfold below_zero_spec.
  simpl.
  split.
  - intro H. discriminate H.
  - intro H. destruct H as [bal [H_in H_lt]].
    repeat destruct H_in as [H_eq | H_in]; subst; try inversion H_lt; try contradiction.
Qed.