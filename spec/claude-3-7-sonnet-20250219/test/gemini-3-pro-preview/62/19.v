Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Open Scope Z_scope.

Definition derivative_spec (xs : list Z) (ds : list Z) : Prop :=
  length ds = pred (length xs) /\
  (forall i : nat, (1 <= i < length xs)%nat -> nth (pred i) ds 0 = nth i xs 0 * Z.of_nat i).

Example test_derivative : derivative_spec [0; 0; -1; 0; 0; 0; 0] [0; -2; 0; 0; 0; 0].
Proof.
  unfold derivative_spec.
  split.
  - (* Check length condition *)
    simpl. reflexivity.
  - (* Check element-wise condition *)
    intros i Hi.
    destruct i.
    + (* i = 0 *)
      lia.
    + destruct i.
      * (* i = 1 *)
        simpl. reflexivity.
      * destruct i.
        -- (* i = 2 *)
           simpl. reflexivity.
        -- destruct i.
           ++ (* i = 3 *)
              simpl. reflexivity.
           ++ destruct i.
              ** (* i = 4 *)
                 simpl. reflexivity.
              ** destruct i.
                 --- (* i = 5 *)
                     simpl. reflexivity.
                 --- destruct i.
                     +++ (* i = 6 *)
                         simpl. reflexivity.
                     +++ (* i >= 7 *)
                         simpl in Hi. lia.
Qed.