Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.

Definition problem_42_pre (input : list Z) : Prop := True.

Definition problem_42_spec(input output : list Z) : Prop :=
  length input = length output /\
  forall i : nat, i < length output -> nth i output 0%Z = ((nth i input 0%Z) + 1)%Z.

Example problem_42_test_1 : problem_42_spec [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z] [2%Z; 3%Z; 4%Z; 5%Z; 6%Z; 7%Z].
Proof.
  unfold problem_42_spec.
  simpl.
  split.
  - reflexivity.
  - intros i Hi.
    destruct i as [|i]; simpl; try lia.
    destruct i as [|i]; simpl; try lia.
    destruct i as [|i]; simpl; try lia.
    destruct i as [|i]; simpl; try lia.
    destruct i as [|i]; simpl; try lia.
    destruct i as [|i]; simpl; try lia.
    exfalso; lia.
Qed.