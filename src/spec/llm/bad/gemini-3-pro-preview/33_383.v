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
  [300; 500; 6; 17; 8; 289; 20; -105; 2; 104; 200; 3; 0; 5; 700; 900; 18; -901; 800; 1000; 0; -277] 
  [-277; 500; 6; 0; 8; 289; 17; -105; 2; 20; 200; 3; 104; 5; 700; 300; 18; -901; 800; 1000; 0; 900].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Destruct i enough times to cover the list length (22) *)
      repeat (destruct i as [|i]; [
        simpl in H; try congruence; simpl; reflexivity
      | ]).
      (* For i >= 22, both are None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-277; 0; 17; 20; 104; 300; 800; 900] [300; 17; 20; 104; 0; 900; 800; -277] *)
        change [300; 17; 20; 104; 0; 900; 800; -277] with ([300; 17; 20; 104; 0; 900; 800] ++ [-277] ++ []).
        apply Permutation_cons_app.
        change [300; 17; 20; 104; 0; 900; 800] with ([300; 17; 20; 104] ++ [0] ++ [900; 800]).
        apply Permutation_cons_app.
        change [300; 17; 20; 104; 900; 800] with ([300] ++ [17] ++ [20; 104; 900; 800]).
        apply Permutation_cons_app.
        change [300; 20; 104; 900; 800] with ([300] ++ [20] ++ [104; 900; 800]).
        apply Permutation_cons_app.
        change [300; 104; 900; 800] with ([300] ++ [104] ++ [900; 800]).
        apply Permutation_cons_app.
        change [300; 900; 800] with ([] ++ [300] ++ [900; 800]).
        apply Permutation_cons_app.
        change [900; 800] with ([900] ++ [800] ++ []).
        apply Permutation_cons_app.
        change [900] with ([] ++ [900] ++ []).
        apply Permutation_cons_app.
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ 
          try apply HdRel_nil; 
          try apply HdRel_cons; 
          compute; try congruence 
        | ]).
        apply Sorted_nil.
Qed.