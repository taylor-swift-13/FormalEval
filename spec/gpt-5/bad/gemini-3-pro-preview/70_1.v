Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Import ListNotations.

Definition index_strange (n k : nat) : nat :=
  if Nat.even k then Nat.div2 k else n - 1 - Nat.div2 k.

Definition ans_of_sorted (s ans : list Z) : Prop :=
  length ans = length s /\
  forall k, k < length s ->
    nth_error ans k = nth_error s (index_strange (length s) k).

Definition strange_sort_list_spec (lst ans : list Z) : Prop :=
  exists s,
    Permutation s lst /\
    Sorted Z.le s /\
    ans_of_sorted s ans.

Example test_strange_sort :
  strange_sort_list_spec [1%Z; 2%Z; 3%Z; 4%Z] [1%Z; 4%Z; 2%Z; 3%Z].
Proof.
  (* We witness the sorted list 's' which happens to be the same as the input list *)
  exists [1%Z; 2%Z; 3%Z; 4%Z].
  
  (* We need to prove 3 things: Permutation, Sorted, and ans_of_sorted *)
  repeat split.
  
  - (* 1. Permutation: since s == input, it is reflexive *)
    apply Permutation_refl.
    
  - (* 2. Sorted: the list is concrete, so we construct the proof *)
    repeat constructor; try lia.
    
  - (* 3a. ans_of_sorted (length): lengths are equal *)
    simpl. reflexivity.
    
  - (* 3b. ans_of_sorted (indices): check mapping for all k *)
    intros k Hk.
    (* We destruct k for each valid index 0, 1, 2, 3.
       The 'do 4' tactic repeats the destruct/solve pattern.
       If k is 0, 1, 2, or 3, 'simpl; reflexivity' solves it.
       If k >= 4, we fall through to the remaining goal. *)
    do 4 (destruct k as [|k]; [ simpl; reflexivity | ]).
    (* For k >= 4, the hypothesis Hk (k < 4) is contradictory *)
    simpl in Hk. lia.
Qed.