Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_43_pre (input : list bool) : Prop := True.

Definition problem_43_spec (input : list bool) (output : bool) : Prop :=
  (exists i j : nat,
    (i <> j) /\
    (i < length input)%nat /\
    (j < length input)%nat /\
    (nth i input false = true) /\
    (nth j input false = false))
  <-> (output = true).

Example test_problem_43 : problem_43_spec [true; true; true; false; false; false; true] true.
Proof.
  unfold problem_43_spec.
  split.
  - intros H.
    reflexivity.
  - intros H.
    exists 0%nat, 3%nat.
    split.
    + lia.
    + split.
      * simpl. lia.
      * split.
        -- simpl. lia.
        -- split.
           ++ simpl. reflexivity.
           ++ simpl. reflexivity.
Qed.