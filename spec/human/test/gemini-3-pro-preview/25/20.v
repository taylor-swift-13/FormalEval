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

Example problem_25_test_case : problem_25_spec 11 [11].
Proof.
  unfold problem_25_spec.
  split.
  - (* Sorted le [11] *)
    apply Sorted_cons.
    + apply Sorted_nil.
    + apply HdRel_nil.
  - split.
    + (* fold_right Nat.mul 1 [11] = 11 *)
      simpl. reflexivity.
    + (* Forall IsPrime [11] *)
      constructor.
      * (* IsPrime 11 *)
        unfold IsPrime. split.
        -- (* 1 < 11 *)
           lia.
        -- (* forall d, 11 mod d = 0 -> d = 1 \/ d = 11 *)
           intros d H.
           destruct (le_gt_dec d 11) as [Hle | Hgt].
           { (* d <= 11 *)
             do 12 (destruct d as [|d]; [ 
               try (simpl in H; discriminate); 
               try (left; reflexivity); 
               try (right; reflexivity) 
             | ]).
             (* d > 11 case, contradictory with Hle *)
             lia.
           }
           { (* d > 11 *)
             apply Nat.mod_small in Hgt.
             rewrite Hgt in H.
             discriminate.
           }
      * (* Forall IsPrime [] *)
        constructor.
Qed.