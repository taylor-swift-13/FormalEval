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

Example test_sort_even_case : sort_even_spec [3; 2; 10; -14; 2; 4; 2; 1; 10] [2; 2; 2; -14; 3; 4; 10; 1; 10].
Proof.
  unfold sort_even_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i Hlen Hodd.
      do 9 (destruct i; [ try (simpl in Hodd; discriminate); try (simpl; reflexivity) | ]).
      simpl in Hlen. lia.
    + split.
      * simpl.
        eapply Permutation_trans.
        2: { apply Permutation_sym. apply (Permutation_middle _ [2; 2] [10; 10] 3). }
        simpl. apply perm_skip.
        eapply Permutation_trans.
        2: { apply Permutation_sym. apply (Permutation_middle _ [2; 2] [10] 10). }
        simpl. apply perm_skip.
        apply Permutation_refl.
      * simpl.
        repeat (apply Sorted_cons; [ apply HdRel_cons; lia | ]).
        apply Sorted_nil.
Qed.