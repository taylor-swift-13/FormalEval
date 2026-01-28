Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Definition problem_42_pre (input : list Z) : Prop := True.

Definition problem_42_spec(input output : list Z) : Prop :=
  length input = length output /\
  forall i : nat, i < length output -> nth i output 0%Z = ((nth i input 0%Z) + 1)%Z.

Example test_problem_42 : problem_42_spec [-1%Z; -5%Z; -3%Z; -5%Z] [0%Z; -4%Z; -2%Z; -4%Z].
Proof.
  unfold problem_42_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    destruct i as [|i'].
    + simpl. reflexivity.
    + destruct i' as [|i''].
      * simpl. reflexivity.
      * destruct i'' as [|i'''].
        -- simpl. reflexivity.
        -- destruct i''' as [|i''''].
           ++ simpl. reflexivity.
           ++ simpl in H. lia.
Qed.