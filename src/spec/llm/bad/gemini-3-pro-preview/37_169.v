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
  [5; -2; -12; 4; 4; 123; 23; 2; 3; 11; 12] 
  [-12; -2; 3; 4; 4; 123; 5; 2; 12; 11; 23].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* We check indices 0 to 10 explicitly. *)
      do 11 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      (* For i >= 11, it contradicts length *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* LHS: [5; -12; 4; 23; 3; 12] *)
        (* RHS: [-12; 3; 4; 5; 12; 23] *)
        
        (* Move 5 (head of LHS) to correct position in RHS *)
        apply Permutation_cons_app with (l1 := [-12; 3; 4]) (l2 := [12; 23]).
        simpl.
        
        (* Match -12 (head of new LHS) with head of new RHS *)
        apply Permutation_cons.
        
        (* Move 4 (head of new LHS) to correct position in RHS *)
        apply Permutation_cons_app with (l1 := [3]) (l2 := [12; 23]).
        simpl.
        
        (* Move 23 (head of new LHS) to correct position in RHS *)
        apply Permutation_cons_app with (l1 := [3; 12]) (l2 := []).
        simpl.
        
        (* Remaining lists are equal *)
        apply Permutation_refl.
        
      * (* 4. Sorted check *)
        simpl.
        (* Check sortedness of [-12; 3; 4; 5; 12; 23] *)
        repeat (apply Sorted_cons; [| simpl; try apply HdRel_nil; try (apply HdRel_cons; lia)]).
        apply Sorted_nil.
Qed.