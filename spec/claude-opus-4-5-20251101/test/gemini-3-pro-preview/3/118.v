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

Example test_below_zero_1 : below_zero_spec [-5; -10; -15; -20; 51; -25; 50; 100] true.
Proof.
  unfold below_zero_spec.
  simpl.
  split.
  - intro H.
    exists (-5).
    split.
    + left. reflexivity.
    + reflexivity.
  - intro H. reflexivity.
Qed.