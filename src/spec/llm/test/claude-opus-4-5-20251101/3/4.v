Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
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

Example test_case : below_zero_spec [1%Z; -1%Z; 2%Z; -2%Z; 5%Z; -5%Z; 4%Z; -4%Z] false.
Proof.
  unfold below_zero_spec.
  simpl.
  split.
  - intro H. discriminate H.
  - intro H. destruct H as [bal [Hin Hlt]].
    destruct Hin as [H1 | [H2 | [H3 | [H4 | [H5 | [H6 | [H7 | [H8 | Hfalse]]]]]]]].
    + rewrite <- H1 in Hlt. lia.
    + rewrite <- H2 in Hlt. lia.
    + rewrite <- H3 in Hlt. lia.
    + rewrite <- H4 in Hlt. lia.
    + rewrite <- H5 in Hlt. lia.
    + rewrite <- H6 in Hlt. lia.
    + rewrite <- H7 in Hlt. lia.
    + rewrite <- H8 in Hlt. lia.
    + destruct Hfalse.
Qed.