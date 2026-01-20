Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition Spec(input output : list Z) : Prop :=
  length input = length output /\
  forall i : nat, i < length output -> nth i output 0%Z = ((nth i input 0%Z) + 1)%Z.

Example incr_list_test_case :
  Spec [10000%Z; 20000%Z; 60000%Z; 70000%Z; 2%Z] [10001%Z; 20001%Z; 60001%Z; 70001%Z; 3%Z].
Proof.
  unfold Spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    repeat (destruct i; [reflexivity| simpl in Hi; apply Lt.lt_S_n in Hi]).
    inversion Hi.
Qed.