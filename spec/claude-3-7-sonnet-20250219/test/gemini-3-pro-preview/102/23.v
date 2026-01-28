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

Example test_choose_num : choose_num_spec 14 14 14.
Proof.
  unfold choose_num_spec.
  (* The spec is structured as A \/ B \/ (C /\ D).
     Since 14 = 14, we need to prove the second branch (B). *)
  right. left.
  
  (* B is x = y /\ (...), so we split. *)
  split.
  
  - (* Prove 14 = 14 *)
    reflexivity.
    
  - (* Logic for choosing 14 from 14 *)
    (* 14 is even, so we take the left branch: even y = true /\ res = y *)
    left.
    split.
    + (* Prove Z.even 14 = true *)
      reflexivity.
    + (* Prove 14 = 14 *)
      reflexivity.
Qed.