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

Ltac solve_perm_concrete :=
  match goal with
  | |- Permutation [] [] => apply Permutation_refl
  | |- Permutation (?x :: ?l) ?r =>
      let H := fresh "H" in
      assert (H: In x r) by (simpl; tauto);
      apply Permutation_cons_ex in H;
      destruct H as [?r' Hperm];
      apply Permutation_trans with (l' := x :: ?r');
      [ apply perm_skip; solve_perm_concrete 
      | apply Permutation_sym; exact Hperm ]
  end.

Example test_case : sort_third_spec 
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 8; 15; 7; 3; 4; 5; 700; 900; 799; -200; -901; 800; 1000; 5; 8; 5] 
  [5; 500; 6; 7; 8; 289; 7; -105; -277; 8; 8; 15; 20; 3; 4; 104; 700; 900; 300; -200; -901; 799; 1000; 5; 800; 5].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 27 (destruct i; [
        simpl in *;
        try (match goal with
             | H : (?x <> 0)%nat |- _ => 
                 let e := eval compute in x in
                 match e with
                 | 0%nat => exfalso; apply H; reflexivity
                 | _ => idtac
                 end
             end);
        try reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl. solve_perm_concrete.
      * simpl.
        repeat (apply Sorted_cons; [
           match goal with
           | |- HdRel _ _ [] => apply HdRel_nil
           | |- HdRel _ _ (_::_) => apply HdRel_cons; simpl; intros C; discriminate
           end
        | ]).
        apply Sorted_nil.
Qed.