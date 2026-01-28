Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

Fixpoint extract_thirds (l : list Z) (i : nat) : list Z :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list Z) (res : list Z) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted Z.le (extract_thirds res 0).

(* Helper lemma to ensure Permutation_cons_app functionality is available *)
Lemma perm_cons_app : forall (A : Type) (l l1 l2 : list A) (a : A),
  l = l1 ++ l2 -> Permutation (a :: l) (l1 ++ a :: l2).
Proof.
  intros. subst. apply Permutation_middle.
Qed.

Example test_case : sort_third_spec 
  [300; 6; 7; 290; 8; 289; 20; -105; -278; 104; 200; 3; 4; 700; -901; 800; 1000; 104; 3] 
  [3; 6; 7; 4; 8; 289; 20; -105; -278; 104; 200; 3; 290; 700; -901; 300; 1000; 104; 800].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We destruct i enough times to cover the list length (19) *)
      do 20 (destruct i; [
        simpl; 
        try reflexivity; (* Matches None=None or Some=Some *)
        (* If reflexivity failed, it means we are at an index divisible by 3 *)
        (* In that case, H says i mod 3 <> 0, so we have a contradiction *)
        exfalso; apply H; vm_compute; reflexivity
      | ]).
      (* For i >= 20, both are None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [3; 4; 20; 104; 290; 300; 800] [300; 290; 20; 104; 4; 800; 3] *)
        (* We match each element from head of LHS in RHS and pull it out *)
        apply perm_cons_app with (l1 := [300; 290; 20; 104; 4; 800]) (l2 := []).
        { reflexivity. }
        simpl.
        apply perm_cons_app with (l1 := [300; 290; 20; 104]) (l2 := [800]).
        { reflexivity. }
        simpl.
        apply perm_cons_app with (l1 := [300; 290]) (l2 := [104; 800]).
        { reflexivity. }
        simpl.
        apply perm_cons_app with (l1 := [300; 290]) (l2 := [800]).
        { reflexivity. }
        simpl.
        apply perm_cons_app with (l1 := [300]) (l2 := [800]).
        { reflexivity. }
        simpl.
        apply perm_cons_app with (l1 := []) (l2 := [800]).
        { reflexivity. }
        simpl.
        apply perm_cons_app with (l1 := []) (l2 := []).
        { reflexivity. }
        apply Permutation_nil.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (constructor; try (unfold Z.le; vm_compute; discriminate)).
Qed.