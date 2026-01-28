Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Fixpoint get_evens (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: [] => [x]
  | x :: _ :: tl => x :: get_evens tl
  end.

Definition sort_even_spec (l res : list Z) : Prop :=
  length l = length res /\
  (forall i : nat, (i < length l)%nat -> Nat.odd i = true -> nth i l 0 = nth i res 0) /\
  Permutation (get_evens l) (get_evens res) /\
  Sorted Z.le (get_evens res).

Example test_sort_even_case : sort_even_spec 
  [1; 2; 3; 4; 4; 6; 7; 8; 2; 4; 3] 
  [1; 2; 2; 4; 3; 6; 3; 8; 4; 4; 7].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate. }
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply perm_skip.
        replace [3; 4; 7; 2; 3] with ([3; 4; 7] ++ 2 :: [3]) by reflexivity.
        assert (H1: Permutation ([3; 4; 7] ++ 2 :: [3]) (2 :: [3; 4; 7; 3])).
        { apply Permutation_sym. replace [3; 4; 7; 3] with ([3; 4; 7] ++ [3]) by reflexivity. apply Permutation_middle. }
        apply (Permutation_trans H1). clear H1.
        apply perm_skip.
        apply perm_skip.
        replace [4; 7; 3] with ([4; 7] ++ 3 :: []) by reflexivity.
        assert (H2: Permutation ([4; 7] ++ 3 :: []) (3 :: [4; 7])).
        { apply Permutation_sym. replace [4; 7] with ([4; 7] ++ []) by reflexivity. apply Permutation_middle. }
        apply (Permutation_trans H2). clear H2.
        apply perm_skip.
        apply Permutation_refl.
      * simpl.
        apply Sorted_cons. apply Sorted_cons. apply Sorted_cons.
        apply Sorted_cons. apply Sorted_cons. apply Sorted_cons.
        apply Sorted_nil.
        apply HdRel_nil.
        apply HdRel_cons. lia.
        apply HdRel_cons. lia.
        apply HdRel_cons. lia.
        apply HdRel_cons. lia.
        apply HdRel_cons. lia.
Qed.