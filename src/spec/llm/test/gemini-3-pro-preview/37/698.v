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

Example test_sort_even_case : sort_even_spec [1; 2; 123; 5; 5; 4; 6; 8] [1; 2; 5; 5; 6; 4; 123; 8].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 8 (destruct i as [|i]; [ simpl in *; try (discriminate || reflexivity) | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        apply perm_skip.
        eapply perm_trans.
        apply perm_swap.
        apply perm_skip.
        apply perm_swap.
      * simpl.
        repeat (apply Sorted_cons; [ | constructor; try lia ]).
        apply Sorted_nil.
Qed.