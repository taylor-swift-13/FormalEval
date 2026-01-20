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
  [-4; 7; 3; -6; 3; 0; 7; -8; -7; 2; 0; 1; 20; 0; 0; 1] 
  [-6; 7; 3; -4; 3; 0; 1; -8; -7; 2; 0; 1; 7; 0; 0; 20].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      do 16 (destruct i; [ simpl in *; try contradiction; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        apply NoDup_Permutation.
        -- (* NoDup LHS *)
           repeat constructor; simpl; intro HIn; 
           repeat (destruct HIn as [HIn|HIn]; [ discriminate | ]); try contradiction.
        -- (* NoDup RHS *)
           repeat constructor; simpl; intro HIn; 
           repeat (destruct HIn as [HIn|HIn]; [ discriminate | ]); try contradiction.
        -- (* In equivalence *)
           intros x. simpl. split; intro HIn;
           repeat (destruct HIn as [HIn|HIn]; [ subst; simpl; tauto | ]); try contradiction.
      * (* Sorted *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_cons; try apply HdRel_nil; compute; try discriminate ]).
        apply Sorted_nil.
Qed.