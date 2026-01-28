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
  [300; 500; 6; 7; 289; 20; -105; -277; 200; 19; 3; 0; 5; 700; -3; 900; 18; -901; 800; 1000; 0; -277]
  [-277; 500; 6; -105; 289; 20; 5; -277; 200; 7; 3; 0; 19; 700; -3; 300; 18; -901; 800; 1000; 0; 900].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check for valid indices within the list length (22 elements) *)
      do 25 (destruct i as [|i]; [
        simpl in *;
        try (exfalso; compute in H; congruence);
        reflexivity
      | ]).
      (* Out of bounds case *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        let rec solve_perm :=
          match goal with
          | |- Permutation [] [] => apply Permutation_nil
          | |- Permutation (?x :: ?xs) ?ys =>
              apply Permutation_Add with (a := x);
              [ repeat (apply Add_cons || apply Add_head)
              | solve_perm ]
          end
        in solve_perm.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; simpl; auto with zarith) ]).
        apply Sorted_nil.
Qed.