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
  [300; 500; 21; 7; 290; 8; 289; 20; -105; -277; 104; 200; 3; 4; 5; 700; 900; -901; 800; 1000; -901] 
  [-277; 500; 21; 3; 290; 8; 7; 20; -105; 289; 104; 200; 300; 4; 5; 700; 900; -901; 800; 1000; -901].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* The list has 21 elements. We destruct i 21 times to handle each index. *)
      do 21 (destruct i; [ 
        simpl in *; 
        try (exfalso; apply H; reflexivity); (* Case where i mod 3 = 0 *)
        try reflexivity (* Case where i mod 3 <> 0 *)
      | ]).
      (* For i >= 21, both lists return None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* We match each element of the sorted list (LHS) to the unsorted list (RHS) explicitly *)
        apply Permutation_cons_app with (l1 := [300; 7; 289]) (l2 := [3; 700; 800]); simpl.
        apply Permutation_cons_app with (l1 := [300; 7; 289]) (l2 := [700; 800]); simpl.
        apply Permutation_cons_app with (l1 := [300]) (l2 := [289; 700; 800]); simpl.
        apply Permutation_cons_app with (l1 := [300]) (l2 := [700; 800]); simpl.
        apply Permutation_cons_app with (l1 := []) (l2 := [700; 800]); simpl.
        apply Permutation_cons_app with (l1 := []) (l2 := [800]); simpl.
        apply Permutation_cons_app with (l1 := []) (l2 := []); simpl.
        constructor.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ | apply HdRel_nil || (apply HdRel_cons; simpl; lia) ]).
        apply Sorted_nil.
Qed.