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

Example test_choose_num : choose_num_spec 22 4 (-1).
Proof.
  unfold choose_num_spec.
  (* Since 22 > 4, we take the first branch of the disjunction *)
  left.
  split.
  - (* Prove 22 > 4 *)
    lia.
  - (* Prove res = -1 *)
    reflexivity.
Qed.