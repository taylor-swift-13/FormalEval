Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_42_pre (input : list Z) : Prop := True.

Definition problem_42_spec(input output : list Z) : Prop :=
  length input = length output /\
  forall i : nat, (i < length output)%nat -> nth i output 0%Z = ((nth i input 0%Z) + 1)%Z.

Example problem_42_example : problem_42_spec [16%Z; 10%Z; 4%Z; 6%Z; 8%Z; 7%Z; 10%Z; 12%Z; 14%Z; 16%Z; 18%Z] [17%Z; 11%Z; 5%Z; 7%Z; 9%Z; 8%Z; 11%Z; 13%Z; 15%Z; 17%Z; 19%Z].
Proof.
  unfold problem_42_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    repeat (destruct i as [|i]; [ simpl; reflexivity | ]).
    simpl in H. lia.
Qed.