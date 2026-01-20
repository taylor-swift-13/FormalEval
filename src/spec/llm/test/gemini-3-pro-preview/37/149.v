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
  [11; -7; 2; 10; 0; 9; 5; -3; 2; 8; 2; 3; 7] 
  [0; -7; 2; 10; 2; 9; 2; -3; 5; 8; 7; 3; 11].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      do 13 (destruct i; [ simpl in Hodd; try discriminate; simpl; reflexivity | ]).
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Current: [11; 2; 0; 5; 2; 2; 7] *)
        (* Target:  [0; 2; 2; 2; 5; 7; 11] *)
        
        (* Move 0 to front *)
        eapply perm_trans. apply perm_skip. apply perm_swap.
        eapply perm_trans. apply perm_swap.
        apply perm_skip.
        
        (* Move 2 to front *)
        eapply perm_trans. apply perm_swap.
        apply perm_skip.

        (* Move 2 to front *)
        eapply perm_trans. apply perm_skip. apply perm_swap.
        eapply perm_trans. apply perm_swap.
        apply perm_skip.

        (* Move 2 to front *)
        eapply perm_trans. apply perm_skip. apply perm_swap.
        eapply perm_trans. apply perm_swap.
        apply perm_skip.
        
        (* Move 5 to front *)
        eapply perm_trans. apply perm_swap.
        apply perm_skip.

        (* Move 7 to front *)
        eapply perm_trans. apply perm_swap.
        apply perm_skip.
        
        apply Permutation_refl.

      * (* 4. Sorted check *)
        simpl.
        repeat (apply Sorted_cons; [ | try (apply HdRel_cons; lia); try apply HdRel_nil ]).
        apply Sorted_nil.
Qed.