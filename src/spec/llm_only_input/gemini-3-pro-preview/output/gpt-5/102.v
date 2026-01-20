Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition choose_num_spec (x y r : Z) : Prop :=
(x > y /\ r = -1) \/
(x <= y /\ (exists k : Z, r = 2 * k) /\ x <= r /\ r <= y /\
 (forall z : Z, (exists k : Z, z = 2 * k) /\ x <= z /\ z <= y -> z <= r)) \/
(x <= y /\ ~ (exists z : Z, (exists k : Z, z = 2 * k) /\ x <= z /\ z <= y) /\ r = -1).

Example test_choose_num : choose_num_spec 12 15 14.
Proof.
  unfold choose_num_spec.
  (* The specification has 3 cases. We prove the middle case holds. *)
  right. left.
  repeat split.
  - (* Prove 12 <= 15 *)
    lia.
  - (* Prove 14 is even *)
    exists 7. reflexivity.
  - (* Prove 12 <= 14 *)
    lia.
  - (* Prove 14 <= 15 *)
    lia.
  - (* Prove 14 is the largest even number in [12, 15] *)
    intros z [[k Hk] [Hmin Hmax]].
    (* Hypotheses: z = 2*k, 12 <= z, z <= 15 *)
    (* Goal: z <= 14 *)
    (* Since z is even and z <= 15, z cannot be 15, so z <= 14 *)
    lia.
Qed.