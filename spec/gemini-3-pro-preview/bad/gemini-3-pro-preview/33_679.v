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

Example test_case : sort_third_spec 
  [300; 500; 6; 7; 291; 8; -3; 289; 20; 104; -277; 8; 104; 200; -8; 700; 900; -901; 800; 1000; 290; -8; 6]
  [-8; 500; 6; -3; 291; 8; 7; 289; 20; 104; -277; 8; 104; 200; -8; 300; 900; -901; 700; 1000; 290; 800; 6].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 23 (destruct i; [ 
        simpl in *; 
        try (exfalso; vm_compute in H; congruence); 
        reflexivity 
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        Ltac solve_perm :=
          match goal with
          | |- Permutation [] [] => apply Permutation_refl
          | |- Permutation (?x :: ?xs) ?ys =>
             let rec aux l1 l2 :=
               match l2 with
               | x :: ?l2' =>
                   replace ys with (l1 ++ x :: l2') by reflexivity;
                   apply Permutation_trans with (l' := x :: (l1 ++ l2'));
                   [ apply Permutation_cons; solve_perm | apply Permutation_middle ]
               | ?y :: ?l2' =>
                   aux (l1 ++ [y]) l2'
               end
             in aux (@nil Z) ys
          end.
        solve_perm.
      * simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_nil || (apply HdRel_cons; apply Z.leb_le; reflexivity) ]).
        apply Sorted_nil.
Qed.