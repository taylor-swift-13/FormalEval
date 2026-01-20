Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition Spec(input output : list Z) : Prop :=
  length input = length output /\
  forall i : nat, i < length output -> nth i output 0%Z = ((nth i input 0%Z) + 1)%Z.

Example incr_list_test_large_numbers :
  Spec [10000%Z; 20000%Z; 30000%Z; 40000%Z; 50000%Z; 60000%Z; 70000%Z; 80000%Z; 90000%Z; 100000%Z; 70000%Z] 
       [10001%Z; 20001%Z; 30001%Z; 40001%Z; 50001%Z; 60001%Z; 70001%Z; 80001%Z; 90001%Z; 100001%Z; 70001%Z].
Proof.
  unfold Spec.
  split.
  - simpl. reflexivity.
  - intros i Hi.
    simpl in Hi.
    repeat (destruct i; [reflexivity | simpl in Hi; apply Lt.lt_S_n in Hi]).
    inversion Hi.
Qed.