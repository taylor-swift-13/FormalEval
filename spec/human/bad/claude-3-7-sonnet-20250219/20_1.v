Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.

Import ListNotations.
Local Open Scope R_scope.

Definition problem_20_pre (input : list R) : Prop := (length input >= 2)%nat.

Definition problem_20_spec (input : list R) (output1 output2 : R) : Prop :=
  (length input >= 2)%nat /\
  In output1 input /\
  In output2 input /\
  output1 <= output2 /\
  (forall i j : nat,
    (i < length input)%nat ->
    (j < length input)%nat ->
    i <> j ->
    Rabs (output1 - output2) <= Rabs (nth i input 0 - nth j input 0)).

Example test_case_20 :
  problem_20_spec
    [1.0; 2.0; 3.9; 4.0; 5.0; 2.2]
    3.9
    4.0.
Proof.
  unfold problem_20_spec.
  repeat split.
  - simpl. omega.
  - simpl. right. right. left. reflexivity.
  - simpl. right. right. right. left. reflexivity.
  - unfold Rle. right. unfold Rgt. apply Rlt_trans with 3.95.
    + apply Rmult_lt_reg_l with 2. lra. 
      replace (2 * 3.9) with 7.8 by lra.
      replace (2 * 3.95) with 7.9 by lra. lra.
    + apply Rmult_lt_reg_l with 2. lra.
      replace (2 * 3.95) with 7.9 by lra.
      replace (2 * 4.0) with 8.0 by lra. lra.
  - intros i j Hi Hj Hneq.
    assert (Hi_bound: (i < 6)%nat) by (simpl in Hi; omega).
    assert (Hj_bound: (j < 6)%nat) by (simpl in Hj; omega).
    assert (Hdiff: Rabs (3.9 - 4.0) = 0.1).
    { unfold Rabs. destruct (Rcase_abs (3.9 - 4.0)).
      - replace (- (3.9 - 4.0)) with 0.1 by lra. reflexivity.
      - replace (3.9 - 4.0) with (-0.1) by lra.
        exfalso. apply (Rge_not_lt (3.9 - 4.0) 0 r). lra. }
    rewrite Hdiff.
    do 6 (destruct i as [|i]; [do 6 (destruct j as [|j]; [omega | idtac | simpl; unfold Rabs; destruct Rcase_abs; lra]) | idtac]); omega.
Qed.