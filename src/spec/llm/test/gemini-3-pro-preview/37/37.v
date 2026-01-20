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

Example test_sort_even_case : sort_even_spec [2; 1; 0; 3; 4; 6; 5] [0; 1; 2; 3; 4; 6; 5].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* We destruct i 7 times to handle indices 0 to 6 explicitly *)
      do 7 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      (* Remaining case i >= 7 *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Goal: Permutation [2; 0; 4; 5] [0; 2; 4; 5] *)
        (* This is exactly a swap of the first two elements *)
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        (* Goal: Sorted Z.le [0; 2; 4; 5] *)
        repeat (apply Sorted_cons; [ | first [ apply HdRel_nil | apply HdRel_cons; lia ] ]).
        apply Sorted_nil.
Qed.