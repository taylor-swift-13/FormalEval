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

Example test_maximum : maximum_spec [1; 2; 3; 3] 1 [3].
Proof.
  unfold maximum_spec.
  split.
  - (* Goal: Sorted Z.le [3] *)
    repeat constructor.
  - split.
    + (* Goal: Z.of_nat (length [3]) = 1 *)
      simpl. reflexivity.
    + (* Goal: exists others, Permutation ... *)
      exists [1; 2; 3].
      split.
      * (* Goal: Permutation [1; 2; 3; 3] ([3] ++ [1; 2; 3]) *)
        simpl.
        apply Permutation_sym.
        apply perm_trans with (l' := [1; 3; 2; 3]).
        -- apply perm_swap.
        -- apply perm_skip. apply perm_swap.
      * (* Goal: forall x y, In x res -> In y others -> x >= y *)
        intros x y HInRes HInOthers.
        destruct HInRes as [Heq | Hfalse].
        -- subst x.
           simpl in HInOthers.
           destruct HInOthers as [H1 | [H2 | [H3 | H4]]].
           ++ subst y. unfold Z.ge. apply Z.le_ge. apply Z.leb_le. reflexivity.
           ++ subst y. unfold Z.ge. apply Z.le_ge. apply Z.leb_le. reflexivity.
           ++ subst y. unfold Z.ge. apply Z.le_ge. apply Z.leb_le. reflexivity.
           ++ contradiction.
        -- contradiction.
Qed.