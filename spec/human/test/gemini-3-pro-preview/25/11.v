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

Example problem_25_test_case : problem_25_spec 28 [2; 2; 7].
Proof.
  unfold problem_25_spec.
  split.
  - (* Sorted le [2; 2; 7] *)
    apply Sorted_cons.
    + apply Sorted_cons.
      * apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
      * constructor. lia.
    + constructor. lia.
  - split.
    + (* fold_right Nat.mul 1 [2; 2; 7] = 28 *)
      simpl. reflexivity.
    + (* Forall IsPrime [2; 2; 7] *)
      assert (Hprime2: IsPrime 2).
      { unfold IsPrime. split.
        - lia.
        - intros d H.
          destruct d as [| d]. { simpl in H. discriminate. }
          destruct d as [| d]. { left. reflexivity. }
          destruct d as [| d]. { right. reflexivity. }
          assert (Hlt: 2 < S (S (S d))) by lia.
          apply Nat.mod_small in Hlt. rewrite Hlt in H. discriminate.
      }
      constructor.
      * exact Hprime2.
      * constructor.
        -- exact Hprime2.
        -- constructor.
           ++ (* IsPrime 7 *)
              unfold IsPrime. split.
              ** lia.
              ** intros d H.
                 destruct d as [| d]. { simpl in H. discriminate. } (* 0 *)
                 destruct d as [| d]. { left. reflexivity. }       (* 1 *)
                 destruct d as [| d]. { simpl in H. discriminate. } (* 2 *)
                 destruct d as [| d]. { simpl in H. discriminate. } (* 3 *)
                 destruct d as [| d]. { simpl in H. discriminate. } (* 4 *)
                 destruct d as [| d]. { simpl in H. discriminate. } (* 5 *)
                 destruct d as [| d]. { simpl in H. discriminate. } (* 6 *)
                 destruct d as [| d]. { right. reflexivity. }      (* 7 *)
                 (* d > 7 *)
                 assert (Hlt: 7 < S (S (S (S (S (S (S (S d)))))))) by lia.
                 apply Nat.mod_small in Hlt. rewrite Hlt in H. discriminate.
           ++ apply Forall_nil.
Qed.