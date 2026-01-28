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

Example test_case_complex : below_zero_spec [5; -10; 15; -20; 25; -30; 35; -40; 45; -50] true.
Proof.
  unfold below_zero_spec.
  simpl.
  split.
  - intro.
    exists (-5).
    split.
    + right. left. reflexivity.
    + reflexivity.
  - intro. reflexivity.
Qed.