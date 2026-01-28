Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition choose_num_spec (x y r : Z) : Prop :=
(x > y /\ r = -1) \/
(x <= y /\ (exists k : Z, r = 2 * k) /\ x <= r /\ r <= y /\
 (forall z : Z, (exists k : Z, z = 2 * k) /\ x <= z /\ z <= y -> z <= r)) \/
(x <= y /\ ~ (exists z : Z, (exists k : Z, z = 2 * k) /\ x <= z /\ z <= y) /\ r = -1).

Example test_choose_num : choose_num_spec 50 59 58.
Proof.
  unfold choose_num_spec.
  (* The case where x <= y and r is the largest even number applies here *)
  right. left.
  repeat split.
  - (* x <= y *)
    lia.
  - (* r is even *)
    exists 29. lia.
  - (* x <= r *)
    lia.
  - (* r <= y *)
    lia.
  - (* r is the largest even number in range *)
    intros z H.
    destruct H as [(k & Heq) (Hge & Hle)].
    (* We know 50 <= z <= 59 and z = 2*k. We must prove z <= 58. *)
    (* Since z <= 59, z could be 59. But 59 is odd. *)
    assert (z <> 59).
    {
      intro H59.
      rewrite H59 in Heq.
      (* 59 = 2 * k is impossible for integer k *)
      lia.
    }
    (* Since z <= 59 and z <> 59, then z <= 58 *)
    lia.
Qed.