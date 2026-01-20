Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

Definition has_close_elements_spec (numbers : list R) (threshold : R) (result : bool) : Prop :=
  let P := exists i j x y,
    Nat.lt i j /\
    nth_error numbers i = Some x /\
    nth_error numbers j = Some y /\
    Rabs (x - y) < threshold in
  (result = true <-> P) /\ (result = false <-> ~ P).

Example test_has_close_elements :
  has_close_elements_spec (1.0 :: 2.0 :: 3.9 :: 4.0 :: 5.0 :: 2.2 :: nil) 0.3 true.
Proof.
  unfold has_close_elements_spec.
  split.
  - split.
    + intros _.
      exists 2%nat, 3%nat, 3.9, 4.0.
      split.
      * apply Nat.lt_succ_diag_r.
      * split.
        -- simpl. reflexivity.
        -- split.
           ++ simpl. reflexivity.
           ++ rewrite Rabs_minus_sym.
              unfold Rabs.
              destruct (Rcase_abs (4.0 - 3.9)) as [H|H].
              ** lra.
              ** lra.
    + intros H. reflexivity.
  - split.
    + intros H. discriminate H.
    + intros H.
      exfalso.
      apply H.
      exists 2%nat, 3%nat, 3.9, 4.0.
      split.
      * apply Nat.lt_succ_diag_r.
      * split.
        -- simpl. reflexivity.
        -- split.
           ++ simpl. reflexivity.
           ++ rewrite Rabs_minus_sym.
              unfold Rabs.
              destruct (Rcase_abs (4.0 - 3.9)) as [Hcase|Hcase].
              ** lra.
              ** lra.
Qed.