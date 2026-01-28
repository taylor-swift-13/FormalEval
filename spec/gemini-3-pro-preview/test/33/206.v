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

Example test_case : sort_third_spec [9; -5; 0; -1; 6; -4; -5; 3; 12; 0] [-5; -5; 0; -1; 6; -4; 0; 3; 12; 9].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We check indices 0 to 10. For indices where i mod 3 <> 0, we check equality.
         For i mod 3 = 0, H is a contradiction. *)
      do 11 (destruct i as [|i]; [ simpl in H; try congruence; simpl; reflexivity | ]).
      (* For i >= 11 *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-5; -1; 0; 9] [9; -1; -5; 0] *)
        apply Permutation_sym.
        (* Goal: Permutation [9; -1; -5; 0] [-5; -1; 0; 9] *)
        apply perm_trans with (l' := [9; -5; -1; 0]).
        { apply perm_skip. apply perm_swap. }
        apply perm_trans with (l' := [-5; 9; -1; 0]).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_trans with (l' := [-1; 9; 0]).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_swap.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* Goal: Sorted Z.le [-5; -1; 0; 9] *)
        repeat (constructor; try discriminate).
Qed.