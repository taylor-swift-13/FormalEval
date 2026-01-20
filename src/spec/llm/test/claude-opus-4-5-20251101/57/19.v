Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition is_increasing (l : list Z) : Prop :=
  forall i j, (0 <= i < j)%nat -> (j < length l)%nat -> 
    nth i l 0 <= nth j l 0.

Definition is_decreasing (l : list Z) : Prop :=
  forall i j, (0 <= i < j)%nat -> (j < length l)%nat -> 
    nth i l 0 >= nth j l 0.

Definition monotonic_spec (l : list Z) (result : bool) : Prop :=
  result = true <-> (is_increasing l \/ is_decreasing l).

Example test_monotonic : monotonic_spec [3%Z; 4%Z; 4%Z] true.
Proof.
  unfold monotonic_spec.
  split.
  - intros _.
    left.
    unfold is_increasing.
    intros i j Hij Hj.
    simpl in Hj.
    simpl.
    destruct i as [|i'].
    + destruct j as [|j'].
      * lia.
      * destruct j' as [|j''].
        -- lia.
        -- destruct j'' as [|j'''].
           ++ lia.
           ++ simpl in Hj. lia.
    + destruct i' as [|i''].
      * destruct j as [|j'].
        -- lia.
        -- destruct j' as [|j''].
           ++ lia.
           ++ destruct j'' as [|j'''].
              ** lia.
              ** simpl in Hj. lia.
      * destruct i'' as [|i'''].
        -- destruct j as [|j'].
           ++ lia.
           ++ destruct j' as [|j''].
              ** lia.
              ** destruct j'' as [|j'''].
                 --- lia.
                 --- simpl in Hj. lia.
        -- simpl in Hj.
           destruct j as [|j'].
           ++ lia.
           ++ destruct j' as [|j''].
              ** lia.
              ** destruct j'' as [|j'''].
                 --- lia.
                 --- simpl in Hj. lia.
  - intros _.
    reflexivity.
Qed.