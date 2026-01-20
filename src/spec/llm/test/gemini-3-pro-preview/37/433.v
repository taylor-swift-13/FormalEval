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
  [-3; 2; 2; 3; 4; 6; 7; 122; 123; 8; 8; 2] 
  [-3; 2; 2; 3; 4; 6; 7; 122; 8; 8; 123; 2].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* We check indices 0 to 11. Odd indices must match, even indices are discarded by odd check. *)
      do 12 (destruct i; [ simpl in Hodd; try discriminate Hodd; simpl; reflexivity | ]).
      (* Index out of bounds *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* The lists share a common prefix [-3; 2; 4; 7]. peel them off *)
        repeat apply perm_skip.
        (* Remaining: [123; 8] vs [8; 123] *)
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        (* Check sortedness of [-3; 2; 4; 7; 8; 123] *)
        repeat (apply Sorted_cons; [ | simpl; try apply HdRel_nil; try (apply HdRel_cons; lia) ]).
        apply Sorted_nil.
Qed.