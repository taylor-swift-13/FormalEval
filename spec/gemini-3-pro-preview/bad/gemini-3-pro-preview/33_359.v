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
  [300; 500; 6; -10; 8; 289; 20; -105; -277; 104; 200; 3; 4; 11; 5; -278; 700; 900; -901; 800; 1000; -105] 
  [-901; 500; 6; -278; 8; 289; -105; -105; -277; -10; 200; 3; 4; 11; 5; 20; 700; 900; 104; 800; 1000; 300].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      (* Check indices 0 to 21 *)
      do 22 (destruct i; [ simpl in *; try (compute in H; congruence); reflexivity | ]).
      (* Out of bounds *)
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        simpl.
        apply Permutation_sym.
        (* Move 300 to front *)
        assert (H1: [-901; -278; -105; -10; 4; 20; 104; 300] = [-901; -278; -105; -10; 4; 20; 104] ++ [300]) by reflexivity.
        rewrite H1; clear H1.
        apply Permutation_trans with (300 :: [-901; -278; -105; -10; 4; 20; 104]).
        2: apply Permutation_middle.
        apply Permutation_skip.
        (* Move -10 to front *)
        assert (H2: [-901; -278; -105; -10; 4; 20; 104] = [-901; -278; -105] ++ -10 :: [4; 20; 104]) by reflexivity.
        rewrite H2; clear H2.
        apply Permutation_trans with (-10 :: [-901; -278; -105] ++ [4; 20; 104]).
        2: apply Permutation_middle.
        apply Permutation_skip.
        (* Move 20 to front *)
        assert (H3: [-901; -278; -105; 4; 20; 104] = [-901; -278; -105; 4] ++ 20 :: [104]) by reflexivity.
        rewrite H3; clear H3.
        apply Permutation_trans with (20 :: [-901; -278; -105; 4] ++ [104]).
        2: apply Permutation_middle.
        apply Permutation_skip.
        (* Move 104 to front *)
        assert (H4: [-901; -278; -105; 4; 104] = [-901; -278; -105; 4] ++ 104 :: []) by reflexivity.
        rewrite H4; clear H4.
        apply Permutation_trans with (104 :: [-901; -278; -105; 4]).
        2: apply Permutation_middle.
        apply Permutation_skip.
        (* Move 4 to front *)
        assert (H5: [-901; -278; -105; 4] = [-901; -278; -105] ++ 4 :: []) by reflexivity.
        rewrite H5; clear H5.
        apply Permutation_trans with (4 :: [-901; -278; -105]).
        2: apply Permutation_middle.
        apply Permutation_skip.
        (* Move -278 to front *)
        assert (H6: [-901; -278; -105] = [-901] ++ -278 :: [-105]) by reflexivity.
        rewrite H6; clear H6.
        apply Permutation_trans with (-278 :: [-901] ++ [-105]).
        2: apply Permutation_middle.
        apply Permutation_skip.
        (* Move -901 to front *)
        assert (H7: [-901; -105] = [] ++ -901 :: [-105]) by reflexivity.
        rewrite H7; clear H7.
        apply Permutation_trans with (-901 :: [-105]).
        2: apply Permutation_middle.
        apply Permutation_skip.
        (* Last element *)
        apply Permutation_refl.
      * (* Sorted *)
        simpl.
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_nil; try (apply HdRel_cons; compute; congruence)]).
        apply Sorted_nil.
Qed.