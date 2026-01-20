Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Micromega.Lia.
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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 105; 4; 5; 700; 900; -200; -901; 800; 1000; 6; 6]
  [-901; 500; 6; 6; 8; 289; 7; -105; -277; 20; 200; 3; 104; 4; 5; 105; 900; -200; 300; 800; 1000; 700; 6].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Since the list is concrete and finite, we can destruct i for all valid indices *)
      do 23 (destruct i; [
        simpl in *; 
        try congruence; (* Solves cases where i mod 3 = 0 (contradiction with H) *)
        reflexivity     (* Solves cases where i mod 3 <> 0 (equality holds) *)
      | ]).
      (* Case i >= 23 *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Since the extracted lists contain distinct elements, we can use NoDup_Permutation *)
        apply NoDup_Permutation.
        -- (* NoDup output *)
           repeat (constructor; simpl; try lia).
        -- (* NoDup input *)
           repeat (constructor; simpl; try lia).
        -- (* Elements match *)
           intros x. simpl. tauto.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* Solve Sorted and HdRel for concrete Z list *)
        repeat (constructor; simpl; try lia).
Qed.