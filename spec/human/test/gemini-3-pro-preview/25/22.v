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

Example problem_25_test_case : problem_25_spec 29 [29].
Proof.
  unfold problem_25_spec.
  split.
  - (* Sorted le [29] *)
    apply Sorted_cons.
    + apply Sorted_nil.
    + apply HdRel_nil.
  - split.
    + (* fold_right Nat.mul 1 [29] = 29 *)
      simpl. reflexivity.
    + (* Forall IsPrime [29] *)
      constructor.
      * (* IsPrime 29 *)
        unfold IsPrime. split.
        -- (* 1 < 29 *)
           lia.
        -- (* forall d, 29 mod d = 0 -> d = 1 \/ d = 29 *)
           intros d H.
           destruct (le_gt_dec d 29).
           ++ (* d <= 29 *)
              destruct d as [|d]. { simpl in H. discriminate. } (* 0 *)
              destruct d as [|d]. { left. reflexivity. } (* 1 *)
              (* Check 2..28 *)
              do 27 (destruct d as [|d]; [ simpl in H; discriminate | ]).
              (* 29 *)
              destruct d as [|d]. { right. reflexivity. }
              (* d > 29 but in d <= 29 branch *)
              lia.
           ++ (* d > 29 *)
              apply Nat.mod_small in g.
              rewrite g in H.
              discriminate.
      * (* Forall IsPrime [] *)
        constructor.
Qed.