Require Import ZArith.
Require Import Psatz.

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

Example test_choose_num : choose_num_spec 27 27 (-1).
Proof.
  unfold choose_num_spec.
  (* 27 = 27, so we target the second branch: x = y *)
  right. left.
  split.
  - (* Prove 27 = 27 *)
    reflexivity.
  - (* Logic for odd number 27 *)
    right.
    split.
    + (* Prove Z.even 27 = false *)
      reflexivity.
    + (* Prove -1 = -1 *)
      reflexivity.
Qed.