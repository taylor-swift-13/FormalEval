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

Example test_maximum : maximum_spec [123; -123; 20; 0; 1; 2; -3] 3 [2; 20; 123].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor.
    + apply Z.leb_le. reflexivity.
    + apply Z.leb_le. reflexivity.
  - split.
    + simpl. reflexivity.
    + exists [-123; 0; 1; -3].
      split.
      * apply Permutation_sym.
        change [123; -123; 20; 0; 1; 2; -3] with ([123; -123; 20; 0; 1] ++ 2 :: [-3]).
        apply Permutation_cons_app. simpl.
        change [123; -123; 20; 0; 1; -3] with ([123; -123] ++ 20 :: [0; 1; -3]).
        apply Permutation_cons_app. simpl.
        apply Permutation_refl.
      * intros x y HInRes HInOthers.
        repeat destruct HInRes as [HInRes | HInRes]; subst;
        repeat destruct HInOthers as [HInOthers | HInOthers]; subst;
        try (apply Z.ge_le_iff; apply Z.leb_le; reflexivity);
        try contradiction.
Qed.