Require Import ZArith.
Require Import Psatz. (* For lia tactic *)

Open Scope Z_scope.

Definition is_simple_power_spec (x : Z) (n : Z) (result : bool) : Prop :=
  result = true <-> exists (k : Z), (0 <= k)%Z /\ (n ^ k = x)%Z.

Example test_case : is_simple_power_spec 15 3 false.
Proof.
  unfold is_simple_power_spec.
  split.
  - intros H.
    discriminate.
  - intros [k [Hge Heq]].
    (* We prove by cases: k < 3 or k >= 3 *)
    assert (k < 3 \/ k >= 3) by lia.
    destruct H as [Hsmall | Hlarge].
    + (* Case k < 3: k can be 0, 1, or 2 *)
      assert (k = 0 \/ k = 1 \/ k = 2) by lia.
      destruct H as [H0 | [H1 | H2]]; subst k; simpl in Heq; discriminate.
    + (* Case k >= 3: 3^k >= 27 > 15 *)
      assert (3 ^ 3 <= 3 ^ k).
      { apply Z.pow_le_mono_r; lia. }
      simpl in H.
      rewrite Heq in H.
      lia.
Qed.