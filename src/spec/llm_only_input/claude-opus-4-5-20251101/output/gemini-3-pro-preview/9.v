Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length result = length numbers /\
  forall i : nat, (i < length numbers)%nat ->
    let prefix := firstn (S i) numbers in
    let current_max := nth i result 0 in
    In current_max prefix /\ Forall (fun x => x <= current_max) prefix.

Example rolling_max_empty : rolling_max_spec [] [].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    inversion H.
Qed.