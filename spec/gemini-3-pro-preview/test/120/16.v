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

Example test_maximum : maximum_spec [1; 2; 3] 1 [3].
Proof.
  unfold maximum_spec.
  split.
  - repeat constructor.
  - split.
    + simpl. reflexivity.
    + exists [1; 2].
      split.
      * simpl.
        apply Permutation_sym.
        apply perm_trans with (l' := [1; 3; 2]).
        -- apply perm_swap.
        -- apply perm_skip. apply perm_swap.
      * intros x y HInRes HInOthers.
        inversion HInRes as [Hx | Hx]; [subst x | contradiction].
        inversion HInOthers as [Hy | Hy].
        -- subst y. apply Z.ge_le_iff. apply Z.leb_le. reflexivity.
        -- inversion Hy as [Hy2 | Hy2]; [subst y | contradiction].
           apply Z.ge_le_iff. apply Z.leb_le. reflexivity.
Qed.