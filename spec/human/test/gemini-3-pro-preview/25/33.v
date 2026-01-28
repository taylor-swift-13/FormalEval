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

Example problem_25_test_case : problem_25_spec 31 [31].
Proof.
  unfold problem_25_spec.
  split.
  - (* Sorted le [31] *)
    apply Sorted_cons.
    + apply Sorted_nil.
    + apply HdRel_nil.
  - split.
    + (* fold_right Nat.mul 1 [31] = 31 *)
      simpl. reflexivity.
    + (* Forall IsPrime [31] *)
      constructor.
      * (* IsPrime 31 *)
        unfold IsPrime. split.
        -- (* 1 < 31 *)
           lia.
        -- (* forall d, 31 mod d = 0 -> d = 1 \/ d = 31 *)
           intros d H.
           destruct d. { simpl in H. discriminate. }
           destruct d. { left. reflexivity. }
           (* Check 2..30 *)
           do 29 (destruct d; [ simpl in H; discriminate | ]).
           (* Check 31 *)
           destruct d. { right. reflexivity. }
           (* Check > 31 *)
           exfalso.
           match goal with
           | H : 31 mod ?x = 0 |- _ =>
             assert (31 < x) by lia;
             rewrite Nat.mod_small in H; [discriminate | assumption]
           end.
      * (* Forall IsPrime [] *)
        constructor.
Qed.