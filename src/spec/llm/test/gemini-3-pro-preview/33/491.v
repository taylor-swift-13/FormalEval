Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Lra.
Import ListNotations.
Open Scope R_scope.

Fixpoint extract_thirds (l : list R) (i : nat) : list R :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list R) (res : list R) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted Rle (extract_thirds res 0).

Example test_case : sort_third_spec 
  [-91.9549202660326%R; 19.13452041495991%R; 19.18319187411889%R; -92.90661646941159%R; 19.18319187411889%R]
  [-92.90661646941159%R; 19.13452041495991%R; 19.18319187411889%R; -91.9549202660326%R; 19.18319187411889%R].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      destruct i. { exfalso. apply H. reflexivity. }
      destruct i. { reflexivity. }
      destruct i. { reflexivity. }
      destruct i. { exfalso. apply H. reflexivity. }
      destruct i. { reflexivity. }
      simpl. reflexivity.
    + split.
      * simpl. apply perm_swap.
      * simpl. apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_nil.
           ++ apply HdRel_nil.
        -- apply HdRel_cons.
           lra.
Qed.