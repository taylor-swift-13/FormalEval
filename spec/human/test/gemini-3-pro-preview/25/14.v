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

Example problem_25_test_case : problem_25_spec 33 [3; 11].
Proof.
  unfold problem_25_spec.
  split.
  - (* Sorted le [3; 11] *)
    apply Sorted_cons.
    + apply Sorted_cons.
      * apply Sorted_nil.
      * apply HdRel_nil.
    + apply HdRel_cons. lia.
  - split.
    + (* fold_right Nat.mul 1 [3; 11] = 33 *)
      simpl. reflexivity.
    + (* Forall IsPrime [3; 11] *)
      constructor.
      * (* IsPrime 3 *)
        unfold IsPrime. split.
        -- lia.
        -- intros d H.
           destruct d as [|d]; [ simpl in H; discriminate | ]. (* 0 *)
           destruct d as [|d]; [ left; reflexivity | ]. (* 1 *)
           destruct d as [|d]; [ simpl in H; discriminate | ]. (* 2 *)
           destruct d as [|d]; [ right; reflexivity | ]. (* 3 *)
           (* d >= 4 *)
           assert (Hlt: 3 < S (S (S (S d)))) by lia.
           apply Nat.mod_small in Hlt.
           rewrite Hlt in H. discriminate.
      * constructor.
        -- (* IsPrime 11 *)
           unfold IsPrime. split.
           ++ lia.
           ++ intros d H.
              destruct d as [|d]; [ simpl in H; discriminate | ]. (* 0 *)
              destruct d as [|d]; [ left; reflexivity | ]. (* 1 *)
              destruct d as [|d]; [ simpl in H; discriminate | ]. (* 2 *)
              destruct d as [|d]; [ simpl in H; discriminate | ]. (* 3 *)
              destruct d as [|d]; [ simpl in H; discriminate | ]. (* 4 *)
              destruct d as [|d]; [ simpl in H; discriminate | ]. (* 5 *)
              destruct d as [|d]; [ simpl in H; discriminate | ]. (* 6 *)
              destruct d as [|d]; [ simpl in H; discriminate | ]. (* 7 *)
              destruct d as [|d]; [ simpl in H; discriminate | ]. (* 8 *)
              destruct d as [|d]; [ simpl in H; discriminate | ]. (* 9 *)
              destruct d as [|d]; [ simpl in H; discriminate | ]. (* 10 *)
              destruct d as [|d]; [ right; reflexivity | ]. (* 11 *)
              (* d >= 12 *)
              assert (Hlt: 11 < S (S (S (S (S (S (S (S (S (S (S (S d)))))))))))) by lia.
              apply Nat.mod_small in Hlt.
              rewrite Hlt in H. discriminate.
        -- constructor.
Qed.