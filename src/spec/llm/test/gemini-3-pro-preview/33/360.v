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
  [900; 2; 7; 11; 9; 3; -7; 11; 0; 1; 13; 6; -2; 19; 1] 
  [-7; 2; 7; -2; 9; 3; 1; 11; 0; 11; 13; 6; 900; 19; 1].
Proof.
  unfold sort_third_spec.
  split.
  - reflexivity.
  - split.
    + intros i H.
      do 15 (destruct i; [ simpl in *; try (exfalso; vm_compute in H; congruence); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_cons_app with (l1:=[900; 11]) (l2:=[1; -2]). simpl.
        apply Permutation_cons_app with (l1:=[900; 11; 1]) (l2:=[]). simpl.
        apply Permutation_cons_app with (l1:=[900; 11]) (l2:=[]). simpl.
        apply Permutation_cons_app with (l1:=[900]) (l2:=[]). simpl.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ | first [ apply HdRel_nil | apply HdRel_cons; compute; discriminate ] ]).
        apply Sorted_nil.
Qed.