Require Import Arith.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_31_pre (n : nat) : Prop := True.

Definition problem_31_spec (n : nat) (output : bool) : Prop :=
  IsPrime n <-> output = true.

Example test_case_2_true : problem_31_spec 2 true.
Proof.
  unfold problem_31_spec, IsPrime.
  split.
  - intro H. reflexivity.
  - intro H.
    split.
    + repeat constructor.
    + intros d Hd.
      destruct d as [|d].
      * simpl in Hd. discriminate.
      * destruct d as [|d].
        { left. reflexivity. }
        { destruct d as [|d].
          { right. reflexivity. }
          { assert (Hlt : 2 < S (S (S d))).
            { repeat constructor. }
            apply Nat.mod_small in Hlt.
            rewrite Hlt in Hd.
            discriminate.
          }
        }
Qed.