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

Example test_case_mixed : below_zero_spec [5; -20; 25; -30; 35; -40; 45; -50; -21; -6] true.
Proof.
  unfold below_zero_spec.
  simpl.
  split.
  - intro.
    exists (-15).
    split.
    + right. left. reflexivity.
    + reflexivity.
  - intro.
    reflexivity.
Qed.