Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_25_pre (input : nat) : Prop := True.

Definition problem_25_spec (input : nat) (output : list nat) : Prop :=
  Sorted le output /\
  fold_right Nat.mul 1 output = input /\
  Forall IsPrime output.

Example test_case_1 : problem_25_spec 2 [2].
Proof.
  unfold problem_25_spec. split.
  - constructor. constructor.
  - split.
    + simpl. reflexivity.
    + constructor.
      * unfold IsPrime. split.
        -- lia.
        -- intros d Hd. destruct d.
           ++ simpl in Hd. lia.
           ++ destruct d.
              ** simpl in Hd. lia.
              ** assert (H: 2 mod (S (S d)) <> 0).
                 { apply Nat.mod_upper_bound. lia. }
                 contradiction.
      * constructor.
Qed.