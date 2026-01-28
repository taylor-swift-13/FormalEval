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
  [300%Z; 500%Z; 6%Z; 7%Z; 8%Z; 289%Z; 20%Z; -105%Z; -277%Z; 200%Z; 3%Z; 0%Z; 5%Z; 700%Z; 900%Z; 18%Z; -901%Z; 800%Z; 1000%Z; 0%Z; 289%Z; -277%Z] 
  [-277%Z; 500%Z; 6%Z; 5%Z; 8%Z; 289%Z; 7%Z; -105%Z; -277%Z; 18%Z; 3%Z; 0%Z; 20%Z; 700%Z; 900%Z; 200%Z; -901%Z; 800%Z; 300%Z; 0%Z; 289%Z; 1000%Z].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      do 22 (destruct i; [ simpl in *; try congruence; reflexivity | ]).
      simpl. reflexivity.
    + split.
      * simpl.
        apply Permutation_sym.
        change [-277; 5; 7; 18; 20; 200; 300; 1000] with ([-277; 5; 7; 18; 20; 200] ++ 300 :: [1000]).
        eapply Permutation_trans. 2: apply Permutation_middle.
        apply perm_skip. simpl.

        change [-277; 5; 7; 18; 20; 200; 1000] with ([-277; 5] ++ 7 :: [18; 20; 200; 1000]).
        eapply Permutation_trans. 2: apply Permutation_middle.
        apply perm_skip. simpl.

        change [-277; 5; 18; 20; 200; 1000] with ([-277; 5; 18] ++ 20 :: [200; 1000]).
        eapply Permutation_trans. 2: apply Permutation_middle.
        apply perm_skip. simpl.

        change [-277; 5; 18; 200; 1000] with ([-277; 5; 18] ++ 200 :: [1000]).
        eapply Permutation_trans. 2: apply Permutation_middle.
        apply perm_skip. simpl.

        change [-277; 5; 18; 1000] with ([-277] ++ 5 :: [18; 1000]).
        eapply Permutation_trans. 2: apply Permutation_middle.
        apply perm_skip. simpl.

        change [-277; 18; 1000] with ([-277] ++ 18 :: [1000]).
        eapply Permutation_trans. 2: apply Permutation_middle.
        apply perm_skip. simpl.

        change [-277; 1000] with ([-277] ++ 1000 :: []).
        eapply Permutation_trans. 2: apply Permutation_middle.
        apply perm_skip. simpl.

        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [| simpl; auto with zarith]).
        apply Sorted_nil.
Qed.