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
  [-4; 7; 3; -6; 1000; 0; -8; -6; 8; 6; 2; 289; 1; 7; -8] 
  [-8; 7; 3; -6; 1000; 0; -4; -6; 8; 1; 2; 289; 6; 7; -8].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 15 (destruct i; [ simpl; try (exfalso; apply H; reflexivity); reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply NoDup_Permutation.
        -- repeat (constructor; [ intro HIn; simpl in HIn; repeat (destruct HIn as [HEq | HIn]; [ inversion HEq | ]); contradiction | ]).
           apply NoDup_nil.
        -- repeat (constructor; [ intro HIn; simpl in HIn; repeat (destruct HIn as [HEq | HIn]; [ inversion HEq | ]); contradiction | ]).
           apply NoDup_nil.
        -- intros x. split; intro HIn; simpl in *; 
           repeat (destruct HIn as [HIn | HIn]; [ rewrite <- HIn; simpl; tauto | ]); try tauto.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_nil; try apply HdRel_cons; unfold Z.le; simpl; intro HC; discriminate ]).
        apply Sorted_nil.
Qed.