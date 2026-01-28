Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_43_pre (input : list Z) : Prop := True.

Definition problem_43_spec (input : list Z) (output : bool) : Prop :=
  (exists i j : nat,
    (i <> j)  /\
    (i < length input)%nat /\
    (j < length input)%nat /\
    (nth i input 0 + nth j input 0 = 0))
  <-> (output = true).

Example test_problem_43 : problem_43_spec [-1000%Z; 2000%Z; -2000%Z; 3000%Z; -3000%Z; -4000%Z; 5000%Z; -5000%Z; 6000%Z; -6000%Z; -7000%Z; 8000%Z; -8000%Z; 9000%Z; -9000%Z; 6%Z; -10000%Z] true.
Proof.
  unfold problem_43_spec.
  split.
  - intros _.
    reflexivity.
  - intros _.
    exists 1%nat, 2%nat.
    split.
    + lia.
    + split.
      * simpl. lia.
      * split.
        -- simpl. lia.
        -- simpl. lia.
Qed.