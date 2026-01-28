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

Example problem_25_test_case : problem_25_spec 2 [2].
Proof.
  unfold problem_25_spec.
  split.
  - (* Sorted le [2] *)
    apply Sorted_cons.
    + apply Sorted_nil.
    + apply HdRel_nil.
  - split.
    + (* fold_right Nat.mul 1 [2] = 2 *)
      simpl. reflexivity.
    + (* Forall IsPrime [2] *)
      constructor.
      * (* IsPrime 2 *)
        unfold IsPrime. split.
        -- (* 1 < 2 *)
           lia.
        -- (* forall d, 2 mod d = 0 -> d = 1 \/ d = 2 *)
           intros d H.
           destruct d as [| d'].
           { (* d = 0. In Coq, n mod 0 = n, so 2 mod 0 = 2. H becomes 2 = 0. *)
             simpl in H. discriminate. }
           destruct d' as [| d''].
           { (* d = 1 *) left. reflexivity. }
           destruct d'' as [| d'''].
           { (* d = 2 *) right. reflexivity. }
           { (* d >= 3 *)
             assert (Hlt: 2 < S (S (S d'''))) by lia.
             apply Nat.mod_small in Hlt.
             rewrite Hlt in H.
             discriminate.
           }
      * (* Forall IsPrime [] *)
        constructor.
Qed.