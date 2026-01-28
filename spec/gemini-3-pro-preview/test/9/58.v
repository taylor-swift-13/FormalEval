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

Example test_rolling_max : rolling_max_spec 
  [10%Z; 5%Z; 20%Z; 30%Z; 25%Z; 20%Z; 10%Z; 21%Z; 10%Z; -1%Z] 
  [10%Z; 10%Z; 20%Z; 30%Z; 30%Z; 30%Z; 30%Z; 30%Z; 30%Z; 30%Z].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 10 (destruct i; [ simpl; split; [ tauto | repeat constructor; lia ] | ]).
    simpl in H; lia.
Qed.