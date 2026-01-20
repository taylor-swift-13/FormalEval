Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope R_scope.

Definition has_close_elements_spec (numbers : list R) (threshold : R) (result : bool) : Prop :=
  result = true <->
  exists (i j : nat),
    (i < length numbers)%nat /\
    (j < length numbers)%nat /\
    i <> j /\
    Rabs (nth i numbers 0 - nth j numbers 0) < threshold.

Example test_has_close_elements:
  has_close_elements_spec [1.0; 2.0; 3.9; 4.0; 5.0; 2.2] 0.3 true.
Proof.
  unfold has_close_elements_spec.
  split.
  - intros _.
    exists 2%nat, 3%nat.
    repeat split.
    + (* i < length *)
      simpl. repeat constructor.
    + (* j < length *)
      simpl. repeat constructor.
    + (* i <> j *)
      intro H. discriminate H.
    + (* Rabs condition *)
      simpl.
      apply Rabs_def1.
      * (* 3.9 - 4.0 < 0.3 *)
        (* Multiply by 10 to work with integers *)
        apply Rmult_lt_reg_r with (r := 10).
        { apply IZR_lt. reflexivity. }
        replace ((3.9 - 4.0) * 10) with (-1) by (field; apply Rgt_not_eq; apply IZR_lt; reflexivity).
        replace (0.3 * 10) with 3 by (field; apply Rgt_not_eq; apply IZR_lt; reflexivity).
        apply IZR_lt. reflexivity.
      * (* -0.3 < 3.9 - 4.0 *)
        apply Rmult_lt_reg_r with (r := 10).
        { apply IZR_lt. reflexivity. }
        replace (-0.3 * 10) with (-3) by (field; apply Rgt_not_eq; apply IZR_lt; reflexivity).
        replace ((3.9 - 4.0) * 10) with (-1) by (field; apply Rgt_not_eq; apply IZR_lt; reflexivity).
        apply IZR_lt. reflexivity.
  - intros _. reflexivity.
Qed.