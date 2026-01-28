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

Example problem_25_test_case : problem_25_spec 4 [2; 2].
Proof.
  unfold problem_25_spec.
  split.
  - (* Sorted le [2; 2] *)
    apply Sorted_cons.
    + apply Sorted_cons.
      * apply Sorted_nil.
      * apply HdRel_nil.
    + apply HdRel_cons.
      apply le_n.
  - split.
    + (* fold_right Nat.mul 1 [2; 2] = 4 *)
      simpl. reflexivity.
    + (* Forall IsPrime [2; 2] *)
      constructor.
      * (* IsPrime 2 *)
        unfold IsPrime. split.
        -- (* 1 < 2 *)
           lia.
        -- (* forall d, 2 mod d = 0 -> d = 1 \/ d = 2 *)
           intros d H.
           destruct d as [| d'].
           { simpl in H. discriminate. }
           destruct d' as [| d''].
           { left. reflexivity. }
           destruct d'' as [| d'''].
           { right. reflexivity. }
           {
             assert (Hlt: 2 < S (S (S d'''))) by lia.
             apply Nat.mod_small in Hlt.
             rewrite Hlt in H.
             discriminate.
           }
      * constructor.
        -- (* IsPrime 2 *)
           unfold IsPrime. split.
           ++ lia.
           ++ intros d H.
              destruct d as [| d'].
              { simpl in H. discriminate. }
              destruct d' as [| d''].
              { left. reflexivity. }
              destruct d'' as [| d'''].
              { right. reflexivity. }
              {
                assert (Hlt: 2 < S (S (S d'''))) by lia.
                apply Nat.mod_small in Hlt.
                rewrite Hlt in H.
                discriminate.
              }
        -- constructor.
Qed.