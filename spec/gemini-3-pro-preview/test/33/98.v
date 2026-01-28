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
  [47; 32; 77; 22; 18; 47; 57; 88; 66; 54] 
  [22; 32; 77; 47; 18; 47; 54; 88; 66; 57].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We check the indices explicitly since the list is finite *)
      do 10 (destruct i; [
        simpl in H |- *;
        try (exfalso; apply H; reflexivity); (* Case i % 3 == 0, contradiction *)
        reflexivity (* Case i % 3 != 0, values match *)
      | ]).
      (* Tail case i >= 10 *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* LHS reduces to [22; 47; 54; 57] *)
        (* RHS reduces to [47; 22; 57; 54] *)
        eapply perm_trans.
        { apply perm_swap. } (* Swap 22 and 47 -> [47; 22; 54; 57] *)
        apply perm_skip. apply perm_skip.
        apply perm_swap. (* Swap 54 and 57 -> [57; 54] *)
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* Goal: Sorted Z.le [22; 47; 54; 57] *)
        repeat (apply Sorted_cons || apply HdRel_cons || apply Sorted_nil || apply HdRel_nil).
        (* Solve inequalities like 22 <= 47 *)
        all: intro Hc; discriminate.
Qed.