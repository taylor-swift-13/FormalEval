Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Import ListNotations.
Open Scope Z_scope.

Definition maximum_spec (arr : list Z) (k : Z) (res : list Z) : Prop :=
  Sorted Z.le res /\
  Z.of_nat (length res) = k /\
  exists (others : list Z),
    Permutation arr (res ++ others) /\
    (forall x y, In x res -> In y others -> x >= y).

Example test_maximum : maximum_spec [1; 2; 2; 3; 4; 5] 4 [2; 3; 4; 5].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor; apply Z.leb_le; reflexivity.
  - split.
    + simpl. reflexivity.
    + exists [1; 2].
      split.
      * apply Permutation_sym.
        assert (H: Permutation ([2; 3; 4; 5] ++ [1; 2]) ([2; 3; 4; 5] ++ [2; 1])).
        { apply Permutation_app_head. apply perm_swap. }
        etransitivity. apply H. clear H.
        simpl.
        change (2 :: 3 :: 4 :: 5 :: 2 :: 1 :: nil) with ((2 :: 3 :: 4 :: 5 :: 2 :: nil) ++ [1]).
        etransitivity. apply Permutation_app_comm.
        simpl.
        apply perm_skip.
        apply perm_skip.
        apply Permutation_sym.
        change (3 :: 4 :: 5 :: 2 :: nil) with ([3; 4; 5] ++ [2]).
        apply Permutation_cons_append.
      * intros x y Hx Hy.
        simpl in Hx; simpl in Hy.
        destruct Hx as [? | [? | [? | [? | ?]]]]; subst;
        destruct Hy as [? | [? | ?]]; subst; try contradiction;
        apply Z.ge_le_iff; apply Z.leb_le; reflexivity.
Qed.