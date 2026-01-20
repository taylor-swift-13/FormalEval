Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition maximum_spec (arr : list Z) (k : Z) (res : list Z) : Prop :=
  Sorted Z.le res /\
  Z.of_nat (length res) = k /\
  exists (others : list Z),
    Permutation arr (res ++ others) /\
    (forall x y, In x res -> In y others -> x >= y).

Example test_maximum : maximum_spec [-3; -4; 5] 3 [-4; -3; 5].
Proof.
  unfold maximum_spec.
  split.
  - (* Sorted Z.le [-4; -3; 5] *)
    repeat constructor; lia.
  - split.
    + (* Z.of_nat (length [-4; -3; 5]) = 3 *)
      simpl. reflexivity.
    + (* exists others such that Permutation and forall condition *)
      exists [].
      split.
      * (* Permutation [-3; -4; 5] ([-4; -3; 5] ++ []) *)
        simpl.
        apply perm_trans with ([-4; -3; 5]).
        -- apply perm_trans with ([-3; -4; 5]).
           ++ apply Permutation_refl.
           ++ apply perm_swap.
        -- apply Permutation_refl.
      * (* forall x y, In x [-4; -3; 5] -> In y [] -> x >= y *)
        intros x y Hx Hy.
        simpl in Hy. contradiction.
Qed.