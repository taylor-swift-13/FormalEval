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

Example test_problem_43 : problem_43_spec [99%Z; 0%Z; 1%Z; 0%Z; 0%Z; 100%Z; 0%Z; 0%Z; 0%Z; -1%Z; 0%Z; -1%Z; -1%Z; 0%Z; 1%Z; -1%Z; 1%Z] true.
Proof.
  unfold problem_43_spec.
  split.
  - intros H.
    reflexivity.
  - intros H.
    exists 2%nat, 9%nat.
    split.
    + lia.
    + split.
      * simpl. lia.
      * split.
        -- simpl. lia.
        -- simpl. lia.
Qed.