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
  [5; 2; 7; 9; 3; -6; 500; 8; 21; -6; 0; 300; 13; 6; -2; 19] 
  [-6; 2; 7; 5; 3; -6; 9; 8; 21; 13; 0; 300; 19; 6; -2; 500].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We check the condition for i from 0 to 16 *)
      do 17 (destruct i; [
        simpl in *;
        try (exfalso; apply H; reflexivity); (* Case i mod 3 = 0, contradiction *)
        try reflexivity (* Case i mod 3 <> 0, equality check *)
      | ]).
      (* Tail case for i >= 17 *)
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-6; 5; 9; 13; 19; 500] [5; 9; 500; -6; 13; 19] *)
        apply Permutation_sym.
        (* Goal: Permutation [5; 9; 500; -6; 13; 19] [-6; 5; 9; 13; 19; 500] *)
        (* Move -6 from middle to front *)
        assert (Hperm: Permutation [5; 9; 500; -6; 13; 19] (-6 :: [5; 9; 500; 13; 19])).
        { change [5; 9; 500; -6; 13; 19] with ([5; 9; 500] ++ -6 :: [13; 19]).
          apply Permutation_sym. apply Permutation_middle. }
        apply Permutation_trans with (1:=Hperm). clear Hperm.
        (* Now match prefixes *)
        apply perm_skip. (* -6 matches *)
        apply perm_skip. (* 5 matches *)
        apply perm_skip. (* 9 matches *)
        (* Goal: Permutation [500; 13; 19] [13; 19; 500] *)
        (* Move 500 from front to back *)
        apply Permutation_cons_app.
        simpl. reflexivity.
      * (* 4. Sortedness of extracted thirds *)
        simpl.
        (* Verify sortedness for [-6; 5; 9; 13; 19; 500] *)
        repeat (apply Sorted_cons; [ | apply HdRel_nil || (apply HdRel_cons; cbv; intros; discriminate) ]).
        apply Sorted_nil.
Qed.