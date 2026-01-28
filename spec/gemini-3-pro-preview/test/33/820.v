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
  [299; 500; 6; 7; 290; 8; 289; 20; -105; -277; 104; 3; 4; 700; 900; -901; 800; 1000; -901; 104]
  [-901; 500; 6; -901; 290; 8; -277; 20; -105; 4; 104; 3; 7; 700; 900; 289; 800; 1000; 299; 104].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Exhaustively check indices 0 to 19 *)
      do 20 (destruct i; [ simpl in *; try (contradiction || reflexivity) | ]).
      (* For indices >= 20, both are None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        (* Left (sorted): [-901; -901; -277; 4; 7; 289; 299] *)
        (* Right (original): [299; 7; 289; -277; 4; -901; -901] *)
        simpl.
        apply Permutation_cons_app with (l1 := [299; 7; 289; -277; 4]) (l2 := [-901]). simpl.
        apply Permutation_cons_app with (l1 := [299; 7; 289; -277; 4]) (l2 := []). simpl.
        apply Permutation_cons_app with (l1 := [299; 7; 289]) (l2 := [4]). simpl.
        apply Permutation_cons_app with (l1 := [299; 7; 289]) (l2 := []). simpl.
        apply Permutation_cons_app with (l1 := [299]) (l2 := [289]). simpl.
        apply Permutation_cons_app with (l1 := [299]) (l2 := []). simpl.
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (constructor; try lia).
Qed.