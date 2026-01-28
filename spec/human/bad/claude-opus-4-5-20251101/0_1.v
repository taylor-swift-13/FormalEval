Require Import List Reals Rbasic_fun.
Require Import Lia.
Import ListNotations.
Open Scope R_scope.

Definition problem_0_pre(threshold : R): Prop :=
  threshold >= 0.

Definition problem_0_spec (numbers : list R) (threshold : R) (output : bool): Prop :=
  (exists (i j : nat) (x y : R),
    i <> j /\
    Nat.lt i (length numbers) /\
    Nat.lt j (length numbers) /\
    nth i numbers 0 = x /\
    nth j numbers 0 = y /\
    Rabs (x - y) <= threshold) <->
    output = true.

Example test_has_close_elements :
  problem_0_spec [1.0%R; 2.0%R; 3.9%R; 4.0%R; 5.0%R; 2.2%R] 0.3%R true.
Proof.
  unfold problem_0_spec.
  split.
  - intros _. reflexivity.
  - intros _.
    exists 2%nat, 3%nat, 3.9%R, 4.0%R.
    split.
    + discriminate.
    + split.
      * simpl. lia.
      * split.
        -- simpl. lia.
        -- split.
           ++ simpl. reflexivity.
           ++ split.
              ** simpl. reflexivity.
              ** unfold Rabs.
                 destruct (Rcase_abs (3.9 - 4.0)) as [H|H].
                 --- lra.
                 --- lra.
Qed.