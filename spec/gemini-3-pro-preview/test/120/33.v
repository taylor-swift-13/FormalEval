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

Example test_maximum : maximum_spec [-1; -3; -2; -3; -4; 10; -5] 2 [-1; 10].
Proof.
  unfold maximum_spec.
  split.
  - (* Goal: Sorted Z.le [-1; 10] *)
    repeat constructor.
    (* Prove -1 <= 10 *)
    apply Z.leb_le. reflexivity.
  - split.
    + (* Goal: Z.of_nat (length [-1; 10]) = 2 *)
      simpl. reflexivity.
    + (* Goal: exists others, Permutation ... *)
      exists [-3; -2; -3; -4; -5].
      split.
      * (* Goal: Permutation [-1; -3; -2; -3; -4; 10; -5] ([-1; 10] ++ [-3; -2; -3; -4; -5]) *)
        simpl.
        apply perm_skip.
        (* Goal: Permutation [-3; -2; -3; -4; 10; -5] [10; -3; -2; -3; -4; -5] *)
        (* We need to move 10 from the middle to the head *)
        apply Permutation_sym.
        change ([-3; -2; -3; -4; 10; -5]) with ([-3; -2; -3; -4] ++ 10 :: [-5]).
        change ([10; -3; -2; -3; -4; -5]) with (10 :: [-3; -2; -3; -4] ++ [-5]).
        apply Permutation_middle.
      * (* Goal: forall x y, In x res -> In y others -> x >= y *)
        intros x y HInRes HInOthers.
        simpl in HInRes.
        destruct HInRes as [Hx | [Hx | Hx]]; [subst x | subst x | contradiction].
        -- (* x = -1 *)
           simpl in HInOthers.
           repeat (destruct HInOthers as [Hy | HInOthers]; [subst y; apply Z.le_ge; apply Z.leb_le; reflexivity | ]).
           contradiction.
        -- (* x = 10 *)
           simpl in HInOthers.
           repeat (destruct HInOthers as [Hy | HInOthers]; [subst y; apply Z.le_ge; apply Z.leb_le; reflexivity | ]).
           contradiction.
Qed.