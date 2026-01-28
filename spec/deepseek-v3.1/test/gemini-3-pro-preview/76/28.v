Require Import ZArith.
Require Import Psatz.

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 81 6 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H. inversion H.
  - intros [k [Hge Heq]].
    (* We prove by contradiction that no such k exists *)
    (* Split into small k and large k *)
    assert (k < 3 \/ k >= 3) by lia.
    destruct H as [Hlt | Hge3].
    + (* Case k < 3: k can be 0, 1, or 2 *)
      assert (k = 0 \/ k = 1 \/ k = 2) by lia.
      destruct H as [-> | [-> | ->]]; simpl in Heq; lia.
    + (* Case k >= 3: 6^k is too large *)
      assert (6 ^ 3 <= 6 ^ k) as Hmono.
      { apply Z.pow_le_mono_r; lia. }
      simpl in Hmono. (* 216 <= 6^k *)
      rewrite Heq in Hmono. (* 216 <= 81 *)
      lia.
Qed.