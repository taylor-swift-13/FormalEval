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

Example test_maximum : maximum_spec [2; 3; 2; 3; 2] 2 [3; 3].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor.
    apply Z.leb_le. reflexivity.
  - split.
    + simpl. reflexivity.
    + exists [2; 2; 2].
      split.
      * simpl.
        apply perm_trans with (l' := [3; 2; 2; 3; 2]).
        { apply perm_swap. }
        apply perm_skip.
        apply perm_trans with (l' := [2; 3; 2; 2]).
        { apply perm_skip. apply perm_swap. }
        apply perm_swap.
      * intros x y HInRes HInOthers.
        simpl in HInRes. destruct HInRes as [Hx | [Hx | Hx]]; [subst x | subst x | contradiction].
        -- simpl in HInOthers. destruct HInOthers as [Hy | [Hy | [Hy | Hy]]]; [subst y | subst y | subst y | contradiction].
           ++ unfold Z.ge. apply Z.le_ge. apply Z.leb_le. reflexivity.
           ++ unfold Z.ge. apply Z.le_ge. apply Z.leb_le. reflexivity.
           ++ unfold Z.ge. apply Z.le_ge. apply Z.leb_le. reflexivity.
        -- simpl in HInOthers. destruct HInOthers as [Hy | [Hy | [Hy | Hy]]]; [subst y | subst y | subst y | contradiction].
           ++ unfold Z.ge. apply Z.le_ge. apply Z.leb_le. reflexivity.
           ++ unfold Z.ge. apply Z.le_ge. apply Z.leb_le. reflexivity.
           ++ unfold Z.ge. apply Z.le_ge. apply Z.leb_le. reflexivity.
Qed.