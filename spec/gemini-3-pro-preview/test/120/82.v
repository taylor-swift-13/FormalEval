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

Example test_maximum : maximum_spec [-1; 11; -2; -3; 10; -5] 3 [-1; 10; 11].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor.
    + apply Z.leb_le. reflexivity.
    + apply Z.leb_le. reflexivity.
  - split.
    + simpl. reflexivity.
    + exists [-2; -3; -5].
      split.
      * apply perm_skip.
        symmetry.
        change (10 :: 11 :: -2 :: -3 :: -5 :: []) with (10 :: (11 :: -2 :: -3 :: []) ++ [-5]).
        change (11 :: -2 :: -3 :: 10 :: -5 :: []) with ((11 :: -2 :: -3 :: []) ++ 10 :: [-5]).
        apply Permutation_middle.
      * intros x y Hx Hy.
        simpl in Hx; destruct Hx as [Hx | [Hx | [Hx | Hx]]]; try contradiction; subst.
        -- simpl in Hy; destruct Hy as [Hy | [Hy | [Hy | Hy]]]; try contradiction; subst;
           apply Z.ge_le_iff; apply Z.leb_le; reflexivity.
        -- simpl in Hy; destruct Hy as [Hy | [Hy | [Hy | Hy]]]; try contradiction; subst;
           apply Z.ge_le_iff; apply Z.leb_le; reflexivity.
        -- simpl in Hy; destruct Hy as [Hy | [Hy | [Hy | Hy]]]; try contradiction; subst;
           apply Z.ge_le_iff; apply Z.leb_le; reflexivity.
Qed.