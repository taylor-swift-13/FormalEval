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

Example test_case_1 : below_zero_spec [5%Z; 15%Z; -20%Z; 25%Z; -30%Z; 35%Z; -40%Z; 45%Z; -50%Z; -21%Z] true.
Proof.
  unfold below_zero_spec.
  simpl.
  split.
  - intro H.
    exists (-5)%Z.
    split.
    + do 4 right. left. reflexivity.
    + reflexivity.
  - intro H. reflexivity.
Qed.