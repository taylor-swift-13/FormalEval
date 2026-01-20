Require Import Coq.Lists.List.
Require Import Coq.Reals.Reals.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope R_scope.

Fixpoint get_evens (l : list R) : list R :=
  match l with
  | [] => []
  | x :: [] => [x]
  | x :: _ :: tl => x :: get_evens tl
  end.

Definition sort_even_spec (l res : list R) : Prop :=
  length l = length res /\
  (forall i : nat, (i < length l)%nat -> Nat.odd i = true -> nth i l 0 = nth i res 0) /\
  Permutation (get_evens l) (get_evens res) /\
  Sorted Rle (get_evens res).

Example test_sort_even_case : sort_even_spec [29.192135197854643%R; 33.66238184288656%R; 29.291147603502964%R] [29.192135197854643%R; 33.66238184288656%R; 29.291147603502964%R].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      destruct i.
      * simpl in Hodd. discriminate Hodd.
      * destruct i.
        -- simpl. reflexivity.
        -- destruct i.
           ++ simpl in Hodd. discriminate Hodd.
           ++ simpl in Hlen. lia.
    + split.
      * simpl. apply Permutation_refl.
      * simpl.
        apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_nil.
           ++ apply HdRel_nil.
        -- apply HdRel_cons.
           lra.
Qed.