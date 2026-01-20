Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition choose_num_spec (x y res : Z) : Prop :=
  (x > y /\ res = -1) \/
  (x = y /\ ((Z.even y = true /\ res = y) \/ (Z.even y = false /\ res = -1))) \/
  (x < y /\
    ((Z.even y = true /\ res = y) \/
     (Z.even y = false /\ res = y - 1))) /\
  (* The result must be within [x, y] or -1 if no even number in [x,y] *)
  (res = -1 \/
   (x <= res /\ res <= y /\ Z.even res = true)).

Example test_choose_num : choose_num_spec 12 15 14.
Proof.
  unfold choose_num_spec.
  right. right.
  split.
  - (* x < y and condition on y *)
    split.
    + lia.
    + right.
      split.
      * simpl. reflexivity.
      * reflexivity.
  - (* result is -1 or within bounds and even *)
    right.
    split.
    + lia.
    + split.
      * lia.
      * simpl. reflexivity.
Qed.