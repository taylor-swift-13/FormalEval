Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

(* Pre: no additional constraints for `factorize` by default *)
Definition problem_25_pre (input : nat) : Prop := True.

Definition problem_25_spec (input : nat) (output : list nat) : Prop :=
  Sorted le output /\
  fold_right Nat.mul 1 output = input /\
  Forall IsPrime output.

Example problem_25_test_case : problem_25_spec 100 [2; 2; 5; 5].
Proof.
  unfold problem_25_spec.
  split.
  - (* Sorted le [2; 2; 5; 5] *)
    repeat constructor; try lia.
  - split.
    + (* fold_right Nat.mul 1 [2; 2; 5; 5] = 100 *)
      simpl. reflexivity.
    + (* Forall IsPrime [2; 2; 5; 5] *)
      repeat constructor.
      * (* IsPrime 2 *)
        unfold IsPrime. split.
        -- lia.
        -- intros d H.
           destruct d as [| [| [| d'] ] ].
           ++ simpl in H. discriminate.
           ++ left. reflexivity.
           ++ right. reflexivity.
           ++ assert (Hlt: 2 < S (S (S d'))) by lia.
              apply Nat.mod_small in Hlt.
              rewrite Hlt in H. discriminate.
      * (* IsPrime 2 *)
        unfold IsPrime. split.
        -- lia.
        -- intros d H.
           destruct d as [| [| [| d'] ] ].
           ++ simpl in H. discriminate.
           ++ left. reflexivity.
           ++ right. reflexivity.
           ++ assert (Hlt: 2 < S (S (S d'))) by lia.
              apply Nat.mod_small in Hlt.
              rewrite Hlt in H. discriminate.
      * (* IsPrime 5 *)
        unfold IsPrime. split.
        -- lia.
        -- intros d H.
           destruct d as [| [| [| [| [| [| d']]]]]].
           ++ simpl in H. discriminate.
           ++ left. reflexivity.
           ++ simpl in H. discriminate.
           ++ simpl in H. discriminate.
           ++ simpl in H. discriminate.
           ++ right. reflexivity.
           ++ assert (Hlt: 5 < S (S (S (S (S (S d')))))) by lia.
              apply Nat.mod_small in Hlt.
              rewrite Hlt in H. discriminate.
      * (* IsPrime 5 *)
        unfold IsPrime. split.
        -- lia.
        -- intros d H.
           destruct d as [| [| [| [| [| [| d']]]]]].
           ++ simpl in H. discriminate.
           ++ left. reflexivity.
           ++ simpl in H. discriminate.
           ++ simpl in H. discriminate.
           ++ simpl in H. discriminate.
           ++ right. reflexivity.
           ++ assert (Hlt: 5 < S (S (S (S (S (S d')))))) by lia.
              apply Nat.mod_small in Hlt.
              rewrite Hlt in H. discriminate.
Qed.