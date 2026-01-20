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

Example test_case : sort_third_spec [11; 33; 44; 55; 66; 77; 88; 32; 77; 11] [11; 33; 44; 11; 66; 77; 55; 32; 77; 88].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Check first 10 indices explicitly, then use length property *)
      do 10 (destruct i as [|i]; [
        simpl in *;
        try (exfalso; compute in H; congruence);
        reflexivity
      | ]).
      (* For i >= 10, both lists return None *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [11; 11; 55; 88] [11; 55; 88; 11] *)
        apply perm_skip.
        (* Goal: Permutation [11; 55; 88] [55; 88; 11] *)
        eapply perm_trans.
        apply perm_swap. (* [11; 55; 88] -> [55; 11; 88] *)
        apply perm_skip.
        apply perm_swap. (* [11; 88] -> [88; 11] *)
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* Goal: Sorted Z.le [11; 11; 55; 88] *)
        repeat (constructor; simpl; try (compute; discriminate)).
Qed.