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
  [300; 500; 6; 7; 289; 20; -105; -277; 200; 19; 3; 699; 0; 5; 700; 900; 18; -901; 800; 1001; 0; -277]
  [-277; 500; 6; -105; 289; 20; 0; -277; 200; 7; 3; 699; 19; 5; 700; 300; 18; -901; 800; 1001; 0; 900].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hi.
      do 22 (destruct i; [
        simpl in Hi;
        try (exfalso; apply Hi; reflexivity);
        simpl; reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        Ltac solve_add :=
          match goal with
          | |- Add ?x (?x :: ?ys) ?ys => apply Add_head
          | |- Add ?x (?y :: ?ys') (?y :: ?ys) => apply Add_cons; solve_add
          end.
        Ltac solve_perm :=
          match goal with
          | |- Permutation [] [] => apply perm_nil
          | |- Permutation (?x :: ?xs) ?ys =>
              apply Permutation_Add with (a := x); [ solve_add | solve_perm ]
          end.
        solve_perm.
      * simpl.
        repeat constructor.
Qed.