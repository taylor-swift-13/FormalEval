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

Example test_maximum : maximum_spec [-2; -3; -3; 10; -5; -5] 4 [-3; -3; -2; 10].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor.
    + apply Z.leb_le. reflexivity.
    + apply Z.leb_le. reflexivity.
    + apply Z.leb_le. reflexivity.
  - split.
    + simpl. reflexivity.
    + exists [-5; -5].
      split.
      * apply perm_trans with (l' := -3 :: -2 :: -3 :: 10 :: -5 :: -5 :: []).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_swap.
      * intros x y HInRes HInOthers.
        simpl in HInRes, HInOthers.
        repeat match goal with
        | [ H : _ \/ _ |- _ ] => destruct H as [H|H]; [subst; clear H | ]
        | [ H : False |- _ ] => contradiction
        end;
        apply Z.ge_le_iff; apply Z.leb_le; reflexivity.
Qed.