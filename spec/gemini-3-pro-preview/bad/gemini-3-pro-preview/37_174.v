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
  [-3; 1; 1; 1; 2; 2; 1; 2; 2; 3; 1; 1] 
  [-3; 1; 1; 1; 1; 2; 1; 2; 2; 3; 2; 1].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* We check each index 0..11. Using do 12 handles the finite cases efficiently. *)
      do 12 (destruct i as [|i]; [ simpl in *; try discriminate; try reflexivity | ]).
      (* Case i >= 12 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Target: [-3; 1; 1; 1; 2; 2] *)
        (* Current: [-3; 1; 2; 1; 2; 1] *)
        apply perm_skip. apply perm_skip.
        (* Current tail: [2; 1; 2; 1] vs [1; 1; 2; 2] *)
        etransitivity. apply perm_swap.
        (* Current tail: [1; 2; 2; 1] vs [1; 1; 2; 2] *)
        apply perm_skip.
        (* Current tail: [2; 2; 1] vs [1; 2; 2] *)
        etransitivity. apply perm_skip. apply perm_swap.
        (* Current tail: [2; 1; 2] vs [1; 2; 2] *)
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [| apply HdRel_cons; lia]).
        apply Sorted_nil.
Qed.