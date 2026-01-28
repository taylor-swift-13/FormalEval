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

Example test_maximum : maximum_spec [-1; -2; -3; -3; 10; 10; -5] 3 [-1; 10; 10].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor.
    + apply Z.leb_le. reflexivity.
    + apply Z.leb_le. reflexivity.
  - split.
    + simpl. reflexivity.
    + exists [-2; -3; -3; -5].
      split.
      * simpl.
        apply perm_skip.
        change [-2; -3; -3; 10; 10; -5] with (([-2; -3; -3] ++ [10; 10]) ++ [-5]).
        change [10; 10; -2; -3; -3; -5] with (([10; 10] ++ [-2; -3; -3]) ++ [-5]).
        apply Permutation_app_tail.
        apply Permutation_app_comm.
      * intros x y HInRes HInOthers.
        simpl in HInRes, HInOthers.
        repeat (destruct HInRes as [<- | HInRes]); repeat (destruct HInOthers as [<- | HInOthers]); try contradiction; try (apply Z.ge_le_iff; apply Z.leb_le; reflexivity).
Qed.