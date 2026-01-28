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

Example test_choose_num : choose_num_spec 21 21 (-1).
Proof.
  unfold choose_num_spec.
  (* The spec is structured as A \/ B \/ (C /\ D).
     Since 21 = 21, we need to prove the second branch (B).
     We use 'right' then 'left' to select the middle disjunct. *)
  right. left.
  
  split.
  - (* Prove 21 = 21 *)
    reflexivity.
  - (* Logic for choosing result when x = y *)
    (* 21 is odd, so we take the right branch: even y = false /\ res = -1 *)
    right.
    split.
    + (* Prove Z.even 21 = false *)
      reflexivity.
    + (* Prove -1 = -1 *)
      reflexivity.
Qed.