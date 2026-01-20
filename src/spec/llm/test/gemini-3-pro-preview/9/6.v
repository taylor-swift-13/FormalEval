Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length result = length numbers /\
  forall i : nat, (i < length numbers)%nat ->
    let prefix := firstn (S i) numbers in
    let current_max := nth i result 0 in
    In current_max prefix /\ Forall (fun x => x <= current_max) prefix.

Example test_rolling_max_descending : rolling_max_spec [5; 4; 3; 2; 1] [5; 5; 5; 5; 5].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    repeat (destruct i as [|i]; [
      simpl; split; [
        repeat (left; reflexivity || right)
      | repeat constructor; lia
      ]
    | ]).
    simpl in H. lia.
Qed.