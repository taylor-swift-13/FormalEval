Require Import ZArith.
Require Import Znumtheory.
Require Import Lia.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example gcd_test_3_7 : gcd_spec 3 7 1.
Proof.
  unfold gcd_spec.
  split.
  - (* Prove Zis_gcd 3 7 1 *)
    constructor.
    + (* 1 divides 3 *)
      exists 3. lia.
    + (* 1 divides 7 *)
      exists 7. lia.
    + (* For any x that divides both 3 and 7, x divides 1 *)
      intros x H3 H7.
      destruct H3 as [q3 Hq3].
      destruct H7 as [q7 Hq7].
      (* We use the fact that 7*1 - 3*2 = 1 *)
      exists (q7 - 2 * q3).
      lia.
  - (* Prove 1 >= 0 *)
    lia.
Qed.