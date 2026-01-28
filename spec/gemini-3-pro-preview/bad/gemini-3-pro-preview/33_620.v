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
  [500; 9; 8; 7; 6; 5; 4; 2; 1; -1; -2; -3; -4; -1; -5; -6; -7; -8; -9; -11]
  [-9; 9; 8; -6; 6; 5; -4; 2; 1; -1; -2; -3; 4; -1; -5; 7; -7; -8; 500; -11].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check indices 0 to 19. If i mod 3 = 0, congruence solves it. Else, reflexivity checks equality. *)
      repeat (destruct i; [ simpl in *; try (compute in H; congruence); reflexivity | ]).
      (* For i >= 20, both are out of bounds (None) *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* The extracted list from l is [500; 7; 4; -1; -4; -6; -9] *)
        (* The extracted list from res is [-9; -6; -4; -1; 4; 7; 500] *)
        (* These are reverses of each other. *)
        assert (Hrev: [500; 7; 4; -1; -4; -6; -9] = rev [-9; -6; -4; -1; 4; 7; 500]) by reflexivity.
        rewrite Hrev.
        apply Permutation_rev.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (constructor; try lia).
Qed.