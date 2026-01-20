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

Definition input := [500; 6; 7; 290; 3; 8; 289; 20; 104; -277; 104; 200; 3; 2; -8; 700; -2; -901; 800; 1000; 7; 500].
Definition output := [-277; 6; 7; 3; 3; 8; 289; 20; 104; 290; 104; 200; 500; 2; -8; 500; -2; -901; 700; 1000; 7; 800].

Ltac solve_perm :=
  match goal with
  | |- Permutation [] [] => apply Permutation_nil
  | |- Permutation (?x :: ?tl) ?r =>
    let H := fresh "H" in
    assert (H: In x r) by (simpl; tauto);
    apply in_split in H;
    destruct H as [l1 [l2 H]];
    rewrite H;
    apply Permutation_trans with (x :: l1 ++ l2);
    [ apply Permutation_skip; solve_perm | apply Permutation_middle ]
  end.

Example test_case : sort_third_spec input output.
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      destruct (le_lt_dec 22 i).
      * rewrite !nth_error_None; simpl; try lia.
      * do 22 (destruct i; [ 
          simpl in H |- *; 
          try (exfalso; lia); 
          reflexivity 
        | ]).
        exfalso; lia.
    + split.
      * unfold input, output.
        simpl.
        solve_perm.
      * unfold output.
        simpl.
        repeat (apply Sorted_cons; [ | simpl; first [ apply HdRel_nil | apply HdRel_cons; lia ] ]).
        apply Sorted_nil.
Qed.