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

Ltac solve_perm :=
  match goal with
  | |- Permutation [] [] => apply Permutation_nil
  | |- Permutation (?x :: ?tl) ?lst =>
     let rec split_at_x l pre :=
       match l with
       | ?h :: ?post => 
           tryif constr_eq h x then
             constr:((pre, post))
           else
             split_at_x post (pre ++ [h])
       end
     in
     let res := split_at_x lst (@nil Z) in
     match res with
     | (?pre, ?post) =>
        apply Permutation_trans with (x :: (pre ++ post));
        [ apply Permutation_cons; solve_perm
        | apply Permutation_middle ]
     end
  end.

Example test_case : sort_third_spec 
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 0; 5; 700; 900; 18; -8; -901; 800; 1000; 0; -277] 
  [-901; 500; 6; 0; 8; 289; 0; -105; -277; 7; 200; 3; 20; 5; 700; 104; 18; -8; 300; 800; 1000; 900; -277].
Proof.
  unfold sort_third_spec.
  split.
  - reflexivity.
  - split.
    + intros i H.
      do 23 (destruct i as [|i]; [
        try (exfalso; vm_compute in H; congruence);
        try (vm_compute; reflexivity)
      | ]).
      vm_compute. reflexivity.
    + split.
      * match goal with |- Permutation ?A ?B =>
          let A' := eval vm_compute in A in
          let B' := eval vm_compute in B in
          change (Permutation A' B')
        end.
        solve_perm.
      * match goal with |- Sorted ?R ?A =>
          let A' := eval vm_compute in A in
          change (Sorted R A')
        end.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try apply HdRel_cons; vm_compute; reflexivity ]).
        apply Sorted_nil.
Qed.