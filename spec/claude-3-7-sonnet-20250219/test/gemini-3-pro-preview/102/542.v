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

Example test_choose_num : choose_num_spec 999 1000 1000.
Proof.
  unfold choose_num_spec.
  (* The spec is structured as A \/ B \/ (C /\ D).
     Since 999 < 1000, we need to prove the third branch.
     We use 'right' twice to bypass the first two disjuncts. *)
  right. right.
  
  (* Now we have a conjunction (C /\ D), so we use split. *)
  split.
  
  - (* Part 1: Verify the selection logic (C) *)
    split.
    + (* Prove 999 < 1000 *)
      lia.
    + (* Logic for choosing 1000 from 1000 *)
      (* 1000 is even, so we take the left branch: even y = true /\ res = y *)
      left.
      split.
      * (* Prove Z.even 1000 = true *)
        reflexivity.
      * (* Prove 1000 = 1000 *)
        reflexivity.
        
  - (* Part 2: Verify the result properties (D) *)
    (* 1000 is not -1, so take the right branch *)
    right.
    split.
    + (* Prove 999 <= 1000 *)
      lia.
    + split.
      * (* Prove 1000 <= 1000 *)
        lia.
      * (* Prove Z.even 1000 = true *)
        reflexivity.
Qed.