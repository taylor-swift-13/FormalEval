Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_42_pre (input : list Z) : Prop := True.

Definition problem_42_spec(input output : list Z) : Prop :=
  length input = length output /\
  forall i : nat, (i < length output)%nat -> nth i output 0%Z = ((nth i input 0%Z) + 1)%Z.

Example problem_42_example : problem_42_spec [10000%Z; 30000%Z; 60000%Z; 70000%Z; 80000%Z; 2%Z; 40000%Z] [10001%Z; 30001%Z; 60001%Z; 70001%Z; 80001%Z; 3%Z; 40001%Z].
Proof.
  unfold problem_42_spec.
  split.
  - simpl.
    reflexivity.
  - intros i H.
    repeat (destruct i; [ simpl; reflexivity | simpl in H ]).
    lia.
Qed.