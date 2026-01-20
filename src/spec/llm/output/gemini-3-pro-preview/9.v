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

Example test_rolling_max_empty : rolling_max_spec [] [].
Proof.
  unfold rolling_max_spec.
  split.
  - (* Case 1: Verify that the lengths of input and output are equal *)
    simpl.
    reflexivity.
  - (* Case 2: Verify the rolling max property for every index i *)
    intros i H.
    simpl in H.
    (* H is (i < 0)%nat, which is a contradiction since i is a natural number *)
    lia.
Qed.