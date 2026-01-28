Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition maximum_spec (arr : list Z) (k : Z) (res : list Z) : Prop :=
  Sorted Z.le res /\
  Z.of_nat (length res) = k /\
  exists (others : list Z),
    Permutation arr (res ++ others) /\
    (forall x y, In x res -> In y others -> x >= y).

Example test_maximum : maximum_spec [-123; 20; 0; 1; 2; -3] 4 [0; 1; 2; 20].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor; apply Z.leb_le; reflexivity.
  - split.
    + simpl. reflexivity.
    + exists [-123; -3].
      split.
      * apply Permutation_trans with (l' := -123 :: [0; 1; 2; 20; -3]).
        { apply perm_skip.
          replace (20 :: [0; 1; 2; -3]) with (20 :: [0; 1; 2] ++ [-3]) by reflexivity.
          replace [0; 1; 2; 20; -3] with ([0; 1; 2] ++ 20 :: [-3]) by reflexivity.
          apply Permutation_middle. }
        { replace (-123 :: [0; 1; 2; 20; -3]) with (-123 :: [0; 1; 2; 20] ++ [-3]) by reflexivity.
          replace [0; 1; 2; 20; -123; -3] with ([0; 1; 2; 20] ++ -123 :: [-3]) by reflexivity.
          apply Permutation_middle. }
      * intros x y Hx Hy.
        simpl in Hx, Hy.
        destruct Hx as [? | [? | [? | [? | ?]]]]; subst;
        destruct Hy as [? | [? | ?]]; subst; try lia; try contradiction.
Qed.