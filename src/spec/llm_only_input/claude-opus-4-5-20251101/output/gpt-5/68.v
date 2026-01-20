Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition pluck_spec (arr : list Z) (res : list Z) : Prop :=
((forall x, In x arr -> Z.even x = false) /\ res = nil) \/
(exists min_even i,
  Z.even min_even = true /\
  In min_even arr /\
  (forall y, In y arr -> Z.even y = true -> Z.le min_even y) /\
  nth_error arr i = Some min_even /\
  (forall j, Nat.lt j i -> nth_error arr j <> Some min_even) /\
  res = min_even :: Z.of_nat i :: nil).

Example pluck_test : pluck_spec [4; 2; 3] [2; 1].
Proof.
  unfold pluck_spec.
  right.
  exists 2, 1%nat.
  split.
  - (* Z.even 2 = true *)
    reflexivity.
  - split.
    + (* In 2 [4; 2; 3] *)
      simpl. right. left. reflexivity.
    + split.
      * (* forall y, In y [4; 2; 3] -> Z.even y = true -> 2 <= y *)
        intros y Hin Heven.
        simpl in Hin.
        destruct Hin as [H | [H | [H | H]]].
        -- subst y. lia.
        -- subst y. lia.
        -- subst y. simpl in Heven. discriminate.
        -- contradiction.
      * split.
        -- (* nth_error [4; 2; 3] 1 = Some 2 *)
           reflexivity.
        -- split.
           ++ (* forall j, j < 1 -> nth_error [4; 2; 3] j <> Some 2 *)
              intros j Hlt.
              destruct j.
              ** simpl. intros H. discriminate.
              ** lia.
           ++ (* [2; 1] = 2 :: Z.of_nat 1 :: nil *)
              reflexivity.
Qed.