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
  [-5; -7; 2; 10; 0; 9; 5; -5; 2; 8; 3; 7; 9] 
  [-5; -7; 0; 10; 2; 9; 2; -5; 3; 8; 5; 7; 9].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      (* We check each index. Since the list is finite and small, we can destruct i repeatedly. *)
      repeat (destruct i; [ try (simpl in Hodd; discriminate Hodd); try reflexivity | ]).
      (* If i is larger than the list length *)
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Input evens:  [-5; 2; 0; 5; 2; 3; 9] *)
        (* Output evens: [-5; 0; 2; 2; 3; 5; 9] *)
        apply Permutation_cons. (* Match -5 *)
        (* Goal: Permutation [2; 0; 5; 2; 3; 9] [0; 2; 2; 3; 5; 9] *)
        eapply Permutation_trans. apply Permutation_swap. simpl. (* Swap 2 and 0 *)
        apply Permutation_cons. (* Match 0 *)
        apply Permutation_cons. (* Match 2 *)
        (* Goal: Permutation [5; 2; 3; 9] [2; 3; 5; 9] *)
        eapply Permutation_trans. apply Permutation_swap. simpl. (* Swap 5 and 2 *)
        apply Permutation_cons. (* Match 2 *)
        (* Goal: Permutation [5; 3; 9] [3; 5; 9] *)
        apply Permutation_swap. (* Swap 5 and 3 to match *)
      * (* 4. Sorted check *)
        simpl.
        (* Output evens: [-5; 0; 2; 2; 3; 5; 9] *)
        repeat apply Sorted_cons.
        -- apply Sorted_nil.
        -- apply HdRel_nil.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
        -- apply HdRel_cons; lia.
Qed.