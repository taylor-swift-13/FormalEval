Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition choose_num_spec (x y r : Z) : Prop :=
(x > y /\ r = -1) \/
(x <= y /\ (exists k : Z, r = 2 * k) /\ x <= r /\ r <= y /\
 (forall z : Z, (exists k : Z, z = 2 * k) /\ x <= z /\ z <= y -> z <= r)) \/
(x <= y /\ ~ (exists z : Z, (exists k : Z, z = 2 * k) /\ x <= z /\ z <= y) /\ r = -1).

Example test_choose_num : choose_num_spec 6 20 20.
Proof.
  unfold choose_num_spec.
  right. left.
  repeat split.
  - (* x <= y *)
    lia.
  - (* r is even *)
    exists 10. lia.
  - (* x <= r *)
    lia.
  - (* r <= y *)
    lia.
  - (* r is the largest even number in range *)
    intros z H.
    destruct H as [(k & Heq) (Hge & Hle)].
    (* We know 6 <= z <= 20. We must prove z <= 20. *)
    (* This follows directly from the hypothesis z <= 20. *)
    lia.
Qed.