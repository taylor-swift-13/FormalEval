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

Example test_sort_even_case : sort_even_spec [0; 3; 4; 6; -1; 10; 0] [-1; 3; 0; 6; 0; 10; 4].
Proof.
  unfold sort_even_spec.
  split.
  - (* Length check *)
    simpl. reflexivity.
  - split.
    + (* Odd indices check *)
      intros i Hlen Hodd.
      do 7 (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* Permutation check *)
        simpl.
        (* Goal: Permutation [0; 4; -1; 0] [-1; 0; 0; 4] *)
        apply Permutation_sym.
        (* Goal: Permutation [-1; 0; 0; 4] [0; 4; -1; 0] *)
        
        (* Match -1 *)
        change [0; 4; -1; 0] with ([0; 4] ++ -1 :: [0]).
        apply Permutation_cons_app.
        
        (* Goal: Permutation [0; 0; 4] ([0; 4] ++ [0]) *)
        (* Match first 0 *)
        change ([0; 4] ++ [0]) with ([] ++ 0 :: [4; 0]).
        apply Permutation_cons_app.
        
        (* Goal: Permutation [0; 4] ([] ++ [4; 0]) *)
        (* Match second 0 *)
        change ([] ++ [4; 0]) with ([4] ++ 0 :: []).
        apply Permutation_cons_app.
        
        (* Goal: Permutation [4] ([4] ++ []) *)
        simpl. apply Permutation_refl.
        
      * (* Sorted check *)
        simpl.
        repeat (apply Sorted_cons || apply Sorted_nil || apply HdRel_cons || apply HdRel_nil || lia).
Qed.