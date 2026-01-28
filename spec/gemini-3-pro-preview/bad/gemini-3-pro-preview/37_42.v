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
  [3; 3; 2; 2; 1; 11; 1; 3; 2] 
  [1; 3; 1; 2; 2; 11; 2; 3; 3].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* We check indices 0 to 8 explicitly to avoid complex proof search *)
      do 9 (destruct i; [ simpl in *; try congruence; reflexivity | ]).
      (* i >= 9 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* l_evens reduces to [3; 2; 1; 1; 2] *)
        (* res_evens reduces to [1; 1; 2; 2; 3] *)
        (* We reorder l_evens to match res_evens step by step *)
        transitivity (3 :: [1; 1; 2; 2]).
        { apply perm_skip.
          transitivity (2 :: [1; 1; 2]).
          { apply perm_skip. apply Permutation_refl. }
          { change [1; 1; 2; 2] with ([1; 1] ++ 2 :: [2]).
            apply Permutation_cons_app. }
        }
        { change [1; 1; 2; 2; 3] with ([1; 1; 2; 2] ++ 3 :: []).
          apply Permutation_cons_app. }
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [| apply HdRel_cons; lia]).
        apply Sorted_nil.
Qed.