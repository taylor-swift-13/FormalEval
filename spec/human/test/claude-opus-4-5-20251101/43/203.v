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

Example test_problem_43 : problem_43_spec [1%Z; 2%Z; 3%Z; -70%Z; 5%Z; -9%Z; 9%Z; -7%Z; -6000%Z; 6000%Z; -10%Z; -12%Z; 5%Z; -9%Z; -70%Z] true.
Proof.
  unfold problem_43_spec.
  split.
  - intros _.
    reflexivity.
  - intros _.
    exists 5%nat, 6%nat.
    split.
    + lia.
    + split.
      * simpl. lia.
      * split.
        -- simpl. lia.
        -- simpl. lia.
Qed.