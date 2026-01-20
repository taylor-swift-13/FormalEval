Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Lia.

Open Scope Z_scope.

Definition sum_list (l : list Z) : Z :=
  fold_right Z.add 0 l.

Definition ceil_div (a b : Z) : Z :=
  (a + b - 1) / b.

Definition max_fill_spec (grid : list (list Z)) (capacity : Z) (result : Z) : Prop :=
  capacity > 0 /\
  (forall row, In row grid -> forall x, In x row -> x = 0 \/ x = 1) /\
  result = fold_right (fun row acc => acc + ceil_div (sum_list row) capacity) 0 grid.

Example max_fill_test :
  max_fill_spec ((0::0::1::1::nil)::(0::0::1::1::nil)::(1::1::0::0::nil)::nil) 1 6.
Proof.
  unfold max_fill_spec.
  split.
  - lia.
  - split.
    + intros row Hrow x Hx.
      simpl in Hrow.
      destruct Hrow as [Hrow | [Hrow | [Hrow | Hrow]]].
      * subst row. simpl in Hx.
        destruct Hx as [Hx | [Hx | [Hx | [Hx | Hx]]]].
        -- left. lia.
        -- left. lia.
        -- right. lia.
        -- right. lia.
        -- contradiction.
      * subst row. simpl in Hx.
        destruct Hx as [Hx | [Hx | [Hx | [Hx | Hx]]]].
        -- left. lia.
        -- left. lia.
        -- right. lia.
        -- right. lia.
        -- contradiction.
      * subst row. simpl in Hx.
        destruct Hx as [Hx | [Hx | [Hx | [Hx | Hx]]]].
        -- right. lia.
        -- right. lia.
        -- left. lia.
        -- left. lia.
        -- contradiction.
      * contradiction.
    + simpl.
      unfold ceil_div, sum_list.
      simpl.
      reflexivity.
Qed.