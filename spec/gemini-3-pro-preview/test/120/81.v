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

Example test_maximum : maximum_spec [-3; -3] 0 [].
Proof.
  unfold maximum_spec.
  split.
  - (* Goal: Sorted Z.le [] *)
    constructor.
  - split.
    + (* Goal: Z.of_nat (length []) = 0 *)
      simpl. reflexivity.
    + (* Goal: exists others, Permutation ... *)
      exists [-3; -3].
      split.
      * (* Goal: Permutation [-3; -3] ([] ++ [-3; -3]) *)
        simpl. apply Permutation_refl.
      * (* Goal: forall x y, In x res -> In y others -> x >= y *)
        intros x y HInRes HInOthers.
        (* res is empty, so HInRes is a contradiction *)
        inversion HInRes.
Qed.