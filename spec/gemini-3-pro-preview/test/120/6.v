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

Example test_maximum : maximum_spec [5; 15; 0; 3; -13; -8; 0] 7 [-13; -8; 0; 0; 3; 5; 15].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor; apply Z.leb_le; reflexivity.
  - split.
    + simpl. reflexivity.
    + exists [].
      split.
      * rewrite app_nil_r.
        transitivity (-13 :: [5; 15; 0; 3; -8; 0]).
        { apply Permutation_sym. apply (Permutation_middle [5; 15; 0; 3] [-8; 0] (-13)). }
        apply perm_skip.
        transitivity (-8 :: [5; 15; 0; 3; 0]).
        { apply Permutation_sym. apply (Permutation_middle [5; 15; 0; 3] [0] (-8)). }
        apply perm_skip.
        transitivity (0 :: [5; 15; 3; 0]).
        { apply Permutation_sym. apply (Permutation_middle [5; 15] [3; 0] 0). }
        apply perm_skip.
        transitivity (0 :: [5; 15; 3]).
        { apply Permutation_sym. apply (Permutation_middle [5; 15; 3] [] 0). }
        apply perm_skip.
        transitivity (3 :: [5; 15]).
        { apply Permutation_sym. apply (Permutation_middle [5; 15] [] 3). }
        apply perm_skip.
        apply Permutation_refl.
      * intros x y HInRes HInOthers. inversion HInOthers.
Qed.