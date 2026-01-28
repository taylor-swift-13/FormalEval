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

Example test_rolling_max_simple : rolling_max_spec [1%Z; 50%Z; 1%Z; 1%Z] [1%Z; 50%Z; 50%Z; 50%Z].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    destruct i as [|i].
    + simpl. split.
      * left. reflexivity.
      * repeat constructor; lia.
    + destruct i as [|i].
      * simpl. split.
        -- right. left. reflexivity.
        -- repeat constructor; lia.
      * destruct i as [|i].
        -- simpl. split.
           ++ right. left. reflexivity.
           ++ repeat constructor; lia.
        -- destruct i as [|i].
           ++ simpl. split.
              ** right. left. reflexivity.
              ** repeat constructor; lia.
           ++ lia.
Qed.