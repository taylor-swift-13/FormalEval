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
  [300; 500; 6; 17; 8; 289; 20; -105; -277; 104; 200; 3; 0; 5; 700; 900; 18; -901; 800; 1000; 0; -277]
  [-277; 500; 6; 0; 8; 289; 17; -105; -277; 20; 200; 3; 104; 5; 700; 300; 18; -901; 800; 1000; 0; 900].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    simpl. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* We destruct i 22 times to cover all indices in the lists. *)
      (* For indices < 22, we check equality. For indices >= 22, both are None. *)
      do 22 (destruct i; [ simpl in *; try contradiction; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        simpl.
        (* Goal: Permutation [-277; 0; 17; 20; 104; 300; 800; 900] [300; 17; 20; 104; 0; 900; 800; -277] *)
        
        (* Move -277 to front *)
        assert (H1: Permutation [300; 17; 20; 104; 0; 900; 800; -277] (-277 :: [300; 17; 20; 104; 0; 900; 800])).
        { replace [300; 17; 20; 104; 0; 900; 800; -277] with ([300; 17; 20; 104; 0; 900; 800] ++ [-277]) by reflexivity.
          apply Permutation_sym. apply Permutation_middle. }
        rewrite H1. apply Permutation_cons. clear H1.

        (* Move 0 to front *)
        assert (H2: Permutation [300; 17; 20; 104; 0; 900; 800] (0 :: [300; 17; 20; 104; 900; 800])).
        { replace [300; 17; 20; 104; 0; 900; 800] with ([300; 17; 20; 104] ++ 0 :: [900; 800]) by reflexivity.
          apply Permutation_sym. apply Permutation_middle. }
        rewrite H2. apply Permutation_cons. clear H2.

        (* Move 17 to front *)
        assert (H3: Permutation [300; 17; 20; 104; 900; 800] (17 :: [300; 20; 104; 900; 800])).
        { replace [300; 17; 20; 104; 900; 800] with ([300] ++ 17 :: [20; 104; 900; 800]) by reflexivity.
          apply Permutation_sym. apply Permutation_middle. }
        rewrite H3. apply Permutation_cons. clear H3.

        (* Move 20 to front *)
        assert (H4: Permutation [300; 20; 104; 900; 800] (20 :: [300; 104; 900; 800])).
        { replace [300; 20; 104; 900; 800] with ([300] ++ 20 :: [104; 900; 800]) by reflexivity.
          apply Permutation_sym. apply Permutation_middle. }
        rewrite H4. apply Permutation_cons. clear H4.

        (* Move 104 to front *)
        assert (H5: Permutation [300; 104; 900; 800] (104 :: [300; 900; 800])).
        { replace [300; 104; 900; 800] with ([300] ++ 104 :: [900; 800]) by reflexivity.
          apply Permutation_sym. apply Permutation_middle. }
        rewrite H5. apply Permutation_cons. clear H5.

        (* Remaining: Permutation [300; 800; 900] [300; 900; 800] *)
        apply Permutation_cons.
        (* Remaining: Permutation [800; 900] [900; 800] *)
        apply perm_swap.

      * (* 4. Sortedness of extracted thirds *)
        simpl.
        repeat (constructor; simpl; try lia).
Qed.