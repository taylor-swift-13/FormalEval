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

Example test_case : sort_third_spec [300; 6; 7; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; 700; 900; -901; 800; 1000; 104; 3] [-901; 6; 7; 4; 8; 289; 20; -105; -277; 104; 200; 3; 104; 700; 900; 290; 800; 1000; 300; 3].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 20 (destruct i; [
        simpl in *;
        try (exfalso; vm_compute in H; congruence);
        reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        eapply perm_trans.
        2: { apply Permutation_middle with (l1 := [300; 290; 20; 104; 4]) (l2 := [104]) (a := -901). }
        apply perm_skip.
        eapply perm_trans.
        2: { apply Permutation_middle with (l1 := [300; 290; 20; 104]) (l2 := [104]) (a := 4). }
        apply perm_skip.
        eapply perm_trans.
        2: { apply Permutation_middle with (l1 := [300; 290]) (l2 := [104; 104]) (a := 20). }
        apply perm_skip.
        eapply perm_trans.
        2: { apply Permutation_middle with (l1 := [300; 290]) (l2 := [104]) (a := 104). }
        apply perm_skip.
        eapply perm_trans.
        2: { apply Permutation_middle with (l1 := [300; 290]) (l2 := []) (a := 104). }
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_nil; apply HdRel_cons; vm_compute; congruence]).
        apply Sorted_nil.
Qed.