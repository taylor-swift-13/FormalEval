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
  [1; 2; 3; -3; 5; -2; 1; 16; -8; 9; -12; 7; 6; 16] 
  [-3; 2; 3; 1; 5; -2; 1; 16; -8; 6; -12; 7; 9; 16].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* We check indices explicitly. The list length is 14. 
         We loop enough times to cover valid indices and one out of bounds. *)
      do 15 (destruct i as [|i]; [ 
        simpl in H; 
        try (contradiction || discriminate); 
        simpl; reflexivity 
      | ]).
      (* For i >= 15, both nth_error are None *)
      simpl. reflexivity.
    + split.
      * simpl.
        (* Goal: Permutation [-3; 1; 1; 6; 9] [1; -3; 1; 9; 6] *)
        eapply perm_trans.
        apply perm_swap. (* [-3; 1; 1; 6; 9] <-> [1; -3; 1; 6; 9] *)
        do 3 apply perm_skip. (* Match 1, -3, 1 prefix *)
        apply perm_swap. (* [6; 9] <-> [9; 6] *)
      * simpl.
        (* Prove sortedness of [-3; 1; 1; 6; 9] *)
        repeat (constructor; try (apply Z.leb_le; reflexivity)).
Qed.