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

Example test_choose_num : choose_num_spec 11 93 92.
Proof.
  unfold choose_num_spec.
  (* The spec is structured as A \/ B \/ (C /\ D).
     Since 11 < 93, we need to prove the third branch.
     We use 'right' twice to bypass the first two disjuncts. *)
  right. right.
  
  (* Now we have a conjunction (C /\ D), so we use split. *)
  split.
  
  - (* Part 1: Verify the selection logic (C) *)
    split.
    + (* Prove 11 < 93 *)
      lia.
    + (* Logic for choosing 92 from 93 *)
      (* 93 is odd, so we take the right branch: even y = false /\ res = y - 1 *)
      right.
      split.
      * (* Prove Z.even 93 = false *)
        reflexivity.
      * (* Prove 92 = 93 - 1 *)
        reflexivity.
        
  - (* Part 2: Verify the result properties (D) *)
    (* 92 is not -1, so take the right branch *)
    right.
    split.
    + (* Prove 11 <= 92 *)
      lia.
    + split.
      * (* Prove 92 <= 93 *)
        lia.
      * (* Prove Z.even 92 = true *)
        reflexivity.
Qed.