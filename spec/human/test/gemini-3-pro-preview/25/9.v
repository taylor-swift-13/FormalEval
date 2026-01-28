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

Example problem_25_test_case : problem_25_spec 10 [2; 5].
Proof.
  unfold problem_25_spec.
  split.
  - (* Sorted le [2; 5] *)
    apply Sorted_cons.
    + apply Sorted_cons.
      * apply Sorted_nil.
      * apply HdRel_nil.
    + apply HdRel_cons. lia.
  - split.
    + (* fold_right Nat.mul 1 [2; 5] = 10 *)
      simpl. reflexivity.
    + (* Forall IsPrime [2; 5] *)
      constructor.
      * (* IsPrime 2 *)
        unfold IsPrime. split.
        -- lia.
        -- intros d H.
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
        -- (* IsPrime 5 *)
           unfold IsPrime. split.
           ++ lia.
           ++ intros d H.
              destruct d as [| d1]. { simpl in H. discriminate. }
              destruct d1 as [| d2]. { left. reflexivity. } (* d=1 *)
              destruct d2 as [| d3]. { compute in H. discriminate. } (* d=2 *)
              destruct d3 as [| d4]. { compute in H. discriminate. } (* d=3 *)
              destruct d4 as [| d5]. { compute in H. discriminate. } (* d=4 *)
              destruct d5 as [| d6]. { right. reflexivity. } (* d=5 *)
              { (* d >= 6 *)
                assert (Hlt: 5 < S (S (S (S (S (S d6)))))) by lia.
                apply Nat.mod_small in Hlt.
                rewrite Hlt in H.
                discriminate.
              }
        -- constructor.
Qed.