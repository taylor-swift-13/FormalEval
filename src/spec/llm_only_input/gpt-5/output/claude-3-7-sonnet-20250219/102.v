Require Import ZArith Lia.

Open Scope Z_scope.

Definition choose_num_spec (x y res : Z) : Prop :=
  (x > y /\ res = -1) \/
  (x = y /\ ((Z.even y = true /\ res = y) \/ (Z.even y = false /\ res = -1))) \/
  (x < y /\
    ((Z.even y = true /\ res = y) \/
     (Z.even y = false /\ res = y - 1))) /\
  (res = -1 \/
   (x <= res /\ res <= y /\ Z.even res = true)).

Example choose_num_spec_test_case :
  choose_num_spec 12%Z 15%Z 14%Z.
Proof.
  unfold choose_num_spec.
  right.
  right.
  split.
  - split.
    + lia.
    + right. split.
      * vm_compute. reflexivity.
      * lia.
  - right. split.
    + lia.
    + split.
      * lia.
      * vm_compute. reflexivity.
Qed.