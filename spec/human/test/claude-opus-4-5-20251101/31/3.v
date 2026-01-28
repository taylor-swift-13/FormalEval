Require Import Arith.
Require Import Lia.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_is_prime_11 : problem_31_spec 11 true.
Proof.
  unfold problem_31_spec.
  unfold IsPrime.
  split.
  - intros _. reflexivity.
  - intros _.
    split.
    + lia.
    + intros d Hmod.
      destruct d as [| [| [| [| [| [| [| [| [| [| [| [| d']]]]]]]]]]]].
      * simpl in Hmod. lia.
      * left. reflexivity.
      * simpl in Hmod. discriminate.
      * simpl in Hmod. discriminate.
      * simpl in Hmod. discriminate.
      * simpl in Hmod. discriminate.
      * simpl in Hmod. discriminate.
      * simpl in Hmod. discriminate.
      * simpl in Hmod. discriminate.
      * simpl in Hmod. discriminate.
      * simpl in Hmod. discriminate.
      * right. reflexivity.
      * assert (S (S (S (S (S (S (S (S (S (S (S (S d'))))))))))) > 11) by lia.
        assert (11 mod S (S (S (S (S (S (S (S (S (S (S (S d'))))))))))) = 11).
        { apply Nat.mod_small. lia. }
        rewrite H0 in Hmod. discriminate.
Qed.