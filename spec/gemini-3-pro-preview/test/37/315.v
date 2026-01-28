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

Example test_sort_even_case : sort_even_spec [-7; 2; 3; 4; 6; 7; 10; 10; 7] [-7; 2; 3; 4; 6; 7; 7; 10; 10].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* We iterate through indices 0 to 8. *)
      do 9 (destruct i; [
        simpl in Hodd; 
        try discriminate Hodd; (* Case even index: odd i = false, contradiction *)
        simpl; reflexivity     (* Case odd index: values match *)
      | ]).
      (* Case i >= 9: length check contradiction *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [-7; 3; 6; 10; 7] [-7; 3; 6; 7; 10] *)
        apply perm_skip. (* Matches -7 *)
        apply perm_skip. (* Matches 3 *)
        apply perm_skip. (* Matches 6 *)
        apply perm_swap. (* Swaps 10 and 7 to match 7 and 10 *)
      * (* 4. Sorted check *)
        simpl.
        (* Goal: Sorted Z.le [-7; 3; 6; 7; 10] *)
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_cons; try apply HdRel_nil; lia]).
        apply Sorted_nil.
Qed.