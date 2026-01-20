Require Import ZArith.
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
  (* The specification is structured as A \/ B \/ (C /\ D).
     For inputs 12, 15, we fall into the third case (x < y).
     We navigate past the first two disjunctions. *)
  right. right.
  
  (* Now we have a conjunction: (x < y /\ Logic) /\ (Bounds Check).
     We split this into two subgoals. *)
  split.
  
  - (* Goal 1: Prove x < y and the selection logic *)
    split.
    + (* Prove 12 < 15 *)
      lia.
    + (* Prove the selection logic part *)
      (* We need to show: (even 15 = true /\ 14 = 15) \/ (even 15 = false /\ 14 = 15 - 1) *)
      (* Since 15 is odd, we choose the right branch *)
      right.
      split.
      * (* Prove Z.even 15 = false *)
        reflexivity.
      * (* Prove 14 = 15 - 1 *)
        reflexivity.
        
  - (* Goal 2: Prove the bounds check and evenness of result *)
    (* We need to show: 14 = -1 \/ (12 <= 14 <= 15 /\ even 14 = true) *)
    (* 14 is not -1, so we choose the right branch *)
    right.
    (* Now we prove the conjunction: 12 <= 14 /\ 14 <= 15 /\ Z.even 14 = true *)
    split.
    + (* Prove 12 <= 14 *)
      lia.
    + split.
      * (* Prove 14 <= 15 *)
        lia.
      * (* Prove Z.even 14 = true *)
        reflexivity.
Qed.