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

Example test_sort_even_case : sort_even_spec [1; 1; 1; 1; 0; 1; 0; 1; 1] [0; 1; 0; 1; 1; 1; 1; 1; 1].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 9 (destruct i as [|i]; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [1; 1; 0; 0; 1] [0; 0; 1; 1; 1] *)
        apply Permutation_trans with (l' := 0 :: [1; 1; 0; 1]).
        { apply Permutation_sym.
          apply Permutation_cons_app with (l1 := [1; 1]) (l2 := [0; 1]).
          simpl. apply Permutation_refl. }
        apply Permutation_cons.
        apply Permutation_trans with (l' := 0 :: [1; 1; 1]).
        { apply Permutation_sym.
          apply Permutation_cons_app with (l1 := [1; 1]) (l2 := [1]).
          simpl. apply Permutation_refl. }
        apply Permutation_cons.
        apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | simpl; try lia ]).
        apply Sorted_nil.
Qed.