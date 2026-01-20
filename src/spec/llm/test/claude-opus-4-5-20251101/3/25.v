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

Example test_negative_balance : below_zero_spec [-1; -3; 6; 7] true.
Proof.
  unfold below_zero_spec.
  simpl.
  split.
  - intro H. exists (-1). split.
    + left. reflexivity.
    + reflexivity.
  - intro H. reflexivity.
Qed.