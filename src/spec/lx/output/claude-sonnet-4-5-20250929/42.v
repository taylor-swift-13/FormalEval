Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.

Definition Spec(input output : list Z) : Prop :=
  length input = length output /\
  forall i : nat, i < length output -> nth i output 0%Z = ((nth i input 0%Z) + 1)%Z.

Example test_incr_list_empty :
  Spec [] [].
Proof.
  unfold Spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    simpl in H.
    lia.
Qed.