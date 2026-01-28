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

Example test_choose_num : choose_num_spec 10 98 98.
Proof.
  unfold choose_num_spec.
  (* The spec is structured as A \/ B \/ (C /\ D).
     Since 10 < 98, we need to prove the third branch. *)
  right. right.
  
  split.
  
  - (* Part 1: Verify the selection logic *)
    split.
    + (* Prove 10 < 98 *)
      lia.
    + (* Logic for choosing 98 from 98 *)
      (* 98 is even, so we take the left branch: even y = true /\ res = y *)
      left.
      split.
      * (* Prove Z.even 98 = true *)
        reflexivity.
      * (* Prove 98 = 98 *)
        reflexivity.
        
  - (* Part 2: Verify the result properties *)
    (* 98 is not -1, so take the right branch *)
    right.
    split.
    + (* Prove 10 <= 98 *)
      lia.
    + split.
      * (* Prove 98 <= 98 *)
        lia.
      * (* Prove Z.even 98 = true *)
        reflexivity.
Qed.