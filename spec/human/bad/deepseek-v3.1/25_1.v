Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

Definition problem_25_spec (input : nat) (output : list nat) : Prop :=
  Sorted le output /\
  fold_right Nat.mul 1 output = input /\
  Forall IsPrime output.

Example factorize_2_correct : problem_25_spec 2 [2].
Proof.
  unfold problem_25_spec.
  split.
  - apply Sorted_cons.
    + apply Sorted_nil.
    + intros x H. inversion H.
  - split.
    + simpl. reflexivity.
    + apply Forall_cons.
      * unfold IsPrime. split.
        -- lia.
        -- intros d Hmod.
           destruct d.
           ++ simpl in Hmod. discriminate.
           ++ destruct d.
              ** left; reflexivity.
              ** right.
                 assert (H : S (S d) > 2) by lia.
                 rewrite <- Nat.mod_small in Hmod.
                 --- discriminate.
                 --- lia.
      * apply Forall_nil.
Qed.