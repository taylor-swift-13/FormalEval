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

Example problem_25_test_case : problem_25_spec 1000 [2; 2; 2; 5; 5; 5].
Proof.
  unfold problem_25_spec.
  split.
  - repeat constructor; try lia.
  - split.
    + simpl. reflexivity.
    + assert (Hprime2: IsPrime 2).
      { unfold IsPrime. split.
        - lia.
        - intros d H.
          destruct d as [|d]. { simpl in H. discriminate. }
          destruct d as [|d]. { left. reflexivity. }
          destruct d as [|d]. { right. reflexivity. }
          assert (Hlt: 2 < S (S (S d))) by lia.
          apply Nat.mod_small in Hlt. rewrite Hlt in H. discriminate.
      }
      assert (Hprime5: IsPrime 5).
      { unfold IsPrime. split.
        - lia.
        - intros d H.
          destruct d as [|d]. { simpl in H. discriminate. }
          destruct d as [|d]. { left. reflexivity. }
          destruct d as [|d]. { simpl in H. discriminate. }
          destruct d as [|d]. { simpl in H. discriminate. }
          destruct d as [|d]. { simpl in H. discriminate. }
          destruct d as [|d]. { right. reflexivity. }
          assert (Hlt: 5 < S (S (S (S (S (S d)))))) by lia.
          apply Nat.mod_small in Hlt. rewrite Hlt in H. discriminate.
      }
      repeat (constructor; try assumption).
Qed.