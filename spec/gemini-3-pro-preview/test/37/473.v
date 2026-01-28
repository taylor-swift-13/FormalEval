Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Fixpoint get_evens (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: [] => [x]
  | x :: _ :: tl => x :: get_evens tl
  end.

Definition sort_even_spec (l res : list Z) : Prop :=
  length l = length res /\
  (forall i : nat, (i < length l)%nat -> Nat.odd i = true -> nth i l 0 = nth i res 0) /\
  Permutation (get_evens l) (get_evens res) /\
  Sorted Z.le (get_evens res).

Example test_sort_even_case : sort_even_spec 
  [4; -2; -12; 4; -5; 23; 122; 3; 11; 12; -10] 
  [-12; -2; -10; 4; -5; 23; 4; 3; 11; 12; 122].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 11 (destruct i as [|i]; [
        simpl in Hodd;
        try discriminate Hodd;
        simpl; reflexivity
      | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        change [4; -12; -5; 122; 11; -10] with ([4] ++ -12 :: [-5; 122; 11; -10]).
        eapply Permutation_trans. apply Permutation_sym. apply Permutation_middle.
        apply perm_skip.
        simpl.
        change [4; -5; 122; 11; -10] with ([4; -5; 122; 11] ++ -10 :: []).
        eapply Permutation_trans. apply Permutation_sym. apply Permutation_middle.
        apply perm_skip.
        simpl.
        change [4; -5; 122; 11] with ([4] ++ -5 :: [122; 11]).
        eapply Permutation_trans. apply Permutation_sym. apply Permutation_middle.
        apply perm_skip.
        simpl.
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_cons; try apply HdRel_nil; lia]).
        apply Sorted_nil.
Qed.