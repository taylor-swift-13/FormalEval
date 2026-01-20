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
  [10; 0; 8; -1; 6; -4; -5; 12; 0] 
  [-5; 0; 8; -1; 6; -4; 10; 12; 0].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices preservation *)
      intros i H.
      (* We check indices 0 through 9 explicitly *)
      do 10 (destruct i; [ simpl in *; try (contradiction || reflexivity) | ]).
      (* For indices >= 10, both lists return None *)
      simpl. reflexivity.
    + split.
      * (* Permutation of extracted thirds *)
        (* Goal: Permutation [-5; -1; 10] [10; -1; -5] *)
        simpl.
        eapply perm_trans.
        { apply perm_skip. apply perm_swap. } (* [-5; 10; -1] *)
        eapply perm_trans.
        { apply perm_swap. } (* [10; -5; -1] *)
        apply perm_skip. apply perm_swap. (* [10; -1; -5] *)
      * (* Sortedness of extracted thirds *)
        simpl.
        repeat (constructor; simpl; try lia).
Qed.