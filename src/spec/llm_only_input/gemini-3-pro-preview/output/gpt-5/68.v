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

Example test_pluck : pluck_spec [4; 2; 3] [2; 1].
Proof.
  unfold pluck_spec.
  right.
  exists 2, 1%nat.
  split.
  - (* Z.even min_even = true *)
    reflexivity.
  - split.
    + (* In min_even arr *)
      simpl. right. left. reflexivity.
    + split.
      * (* min_even is smaller than other evens *)
        intros y Hin Heven.
        simpl in Hin.
        destruct Hin as [H | [H | [H | H]]]; subst.
        -- (* y = 4 *)
           lia.
        -- (* y = 2 *)
           lia.
        -- (* y = 3 *)
           simpl in Heven. discriminate.
        -- (* False *)
           contradiction.
      * split.
        -- (* nth_error arr i = Some min_even *)
           reflexivity.
        -- split.
           ++ (* First occurrence check *)
              intros j Hlt.
              destruct j.
              ** (* j = 0 *)
                 simpl. discriminate.
              ** (* j >= 1 *)
                 lia.
           ++ (* Result construction *)
              simpl. reflexivity.
Qed.