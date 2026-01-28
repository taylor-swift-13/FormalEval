Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 8192 4 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate.
  - intros [k [Hk1 Hk2]].
    (* We prove by contradiction that no such k exists. *)
    (* We split cases based on whether k < 7 or k >= 7. *)
    assert (H : k < 7 \/ k >= 7) by lia.
    destruct H as [Hlt | Hge].
    + (* Case k < 7 implies k <= 6. We show 4^k <= 4^6 = 4096 < 8192. *)
      assert (Hpow : 4 ^ k <= 4 ^ 6).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hk2 in Hpow.
      simpl in Hpow.
      lia.
    + (* Case k >= 7. We show 4^k >= 4^7 = 16384 > 8192. *)
      assert (Hpow : 4 ^ 7 <= 4 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      rewrite Hk2 in Hpow.
      simpl in Hpow.
      lia.
Qed.