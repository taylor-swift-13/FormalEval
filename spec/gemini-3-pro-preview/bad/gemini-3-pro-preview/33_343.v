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
  [19; 0; -901; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 17; 18; 19; 104; 20; 6] 
  [2; 0; -901; 5; 3; 4; 6; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 17; 18; 19; 104; 20; 19].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We destruct i enough times to cover the list length (25) *)
      do 30 (destruct i; [ simpl in H; try discriminate; simpl; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [2; 5; 6; 8; 11; 14; 17; 19; 19] [19; 2; 5; 8; 11; 14; 17; 19; 6] *)
        apply perm_swap. constructor.
        apply perm_swap. constructor.
        transitivity (6 :: [19; 8; 11; 14; 17; 19]).
        2: { apply (Permutation_middle _ [19; 8; 11; 14; 17; 19] [] 6). }
        constructor.
        apply perm_swap. constructor.
        apply perm_swap. constructor.
        apply perm_swap. constructor.
        apply perm_swap. constructor.
        apply Permutation_refl.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; lia | ]).
        apply Sorted_nil.
Qed.