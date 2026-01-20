Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 105; 4; 5; 700; 900; -200; -901; 800; 1000; 6; 300] 
  [-901; 500; 6; 6; 8; 289; 7; -105; -277; 20; 200; 3; 104; 4; 5; 105; 900; -200; 300; 800; 1000; 700; 300].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 23 (destruct i; [ simpl in *; try contradiction; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl. apply NoDup_Permutation.
        -- repeat (constructor; [ simpl; intro H0; repeat destruct H0; discriminate | ]).
           apply NoDup_nil.
        -- repeat (constructor; [ simpl; intro H0; repeat destruct H0; discriminate | ]).
           apply NoDup_nil.
        -- intros x. simpl. split; intro H0; repeat destruct H0; subst; auto 10.
      * simpl.
        repeat (apply Sorted_cons; [ | solve [ apply HdRel_nil | apply HdRel_cons; lia ] ]).
        apply Sorted_nil.
Qed.