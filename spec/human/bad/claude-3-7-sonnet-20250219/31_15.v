Require Import Arith.
Require Import Lia.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_is_prime_2 :
  problem_31_spec 2 true.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  - intros [Hgt Hdiv].
    reflexivity.
  - intros H.
    subst output.
    split.
    + lia.
    + intros d Hmod.
      assert (d = 0 \/ d > 0) by lia.
      destruct H0 as [Hd0 | Hdpos].
      * subst d. rewrite Nat.mod_0_l in Hmod; [discriminate| lia].
      * destruct d.
        { exfalso; lia. }
        destruct d.
        { left; reflexivity. }
        destruct d.
        { right; reflexivity. }
        assert (2 mod (S (S (S 0))) <> 0).
        { simpl. lia. }
        exfalso. apply H1. exact Hmod.
Qed.