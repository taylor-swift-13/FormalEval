Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition Spec(input output : list Z) : Prop :=
  length input = length output /\
  forall i : nat, i < length output -> nth i output 0%Z = ((nth i input 0%Z) + 1)%Z.

Example incr_list_test_case :
  Spec [1%Z; 4%Z; 6%Z; 8%Z; 10%Z; 20%Z; 16%Z; 14%Z; 4%Z; 20%Z; 7%Z; 6%Z]
       [2%Z; 5%Z; 7%Z; 9%Z; 11%Z; 21%Z; 17%Z; 15%Z; 5%Z; 21%Z; 8%Z; 7%Z].
Proof.
  unfold Spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    repeat (destruct i; [reflexivity| simpl in Hi; apply Lt.lt_S_n in Hi]).
    inversion Hi.
Qed.