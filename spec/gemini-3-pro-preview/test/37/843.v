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

Example test_sort_even_case : sort_even_spec [5; 0; 5; -1; 5; 5; 0] [0; 0; 5; -1; 5; 5; 5].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      repeat (destruct i as [|i]; [ simpl in *; try discriminate; try reflexivity | simpl in Hlen; try lia ]).
    + split.
      * (* 3. Permutation check *)
        simpl.
        apply perm_trans with (l' := [5; 5; 0; 5]).
        { apply perm_skip. apply perm_skip. apply perm_swap. }
        apply perm_trans with (l' := [5; 0; 5; 5]).
        { apply perm_skip. apply perm_swap. }
        apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons || apply HdRel_cons || apply Sorted_nil || apply HdRel_nil || lia).
Qed.