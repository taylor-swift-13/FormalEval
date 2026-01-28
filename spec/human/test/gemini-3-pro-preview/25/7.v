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

Example problem_25_test_case : problem_25_spec 20577 [3; 19; 19; 19].
Proof.
  unfold problem_25_spec.
  split.
  - (* Sorted le [3; 19; 19; 19] *)
    apply Sorted_cons.
    + apply Sorted_cons.
      * apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_nil.
           ++ apply HdRel_nil.
        -- apply HdRel_cons; lia.
      * apply HdRel_cons; lia.
    + apply HdRel_cons; lia.
  - split.
    + (* fold_right Nat.mul 1 [3; 19; 19; 19] = 20577 *)
      simpl. reflexivity.
    + (* Forall IsPrime [3; 19; 19; 19] *)
      assert (P3: IsPrime 3).
      {
        unfold IsPrime. split; [lia|].
        intros d H.
        do 4 (destruct d as [|d]; [ simpl in H; try discriminate; try (left; reflexivity); try (right; reflexivity) | ]).
        match type of H with | _ mod ?b = 0 => assert (Hlt: 3 < b) by lia end.
        apply Nat.mod_small in Hlt. rewrite Hlt in H. discriminate.
      }
      assert (P19: IsPrime 19).
      {
        unfold IsPrime. split; [lia|].
        intros d H.
        do 20 (destruct d as [|d]; [ simpl in H; try discriminate; try (left; reflexivity); try (right; reflexivity) | ]).
        match type of H with | _ mod ?b = 0 => assert (Hlt: 19 < b) by lia end.
        apply Nat.mod_small in Hlt. rewrite Hlt in H. discriminate.
      }
      constructor; [exact P3|].
      constructor; [exact P19|].
      constructor; [exact P19|].
      constructor; [exact P19|].
      constructor.
Qed.