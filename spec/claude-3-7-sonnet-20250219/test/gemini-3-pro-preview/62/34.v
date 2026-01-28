Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

(* 
   The specification defines the relationship between the coefficients of a polynomial 'xs'
   and the coefficients of its derivative 'ds'.
   'xs' = [c_0; c_1; c_2; ...], corresponding to c_0 + c_1*x + c_2*x^2 + ...
   'ds' = [d_0; d_1; ...], corresponding to d_0 + d_1*x + ...
   The relationship is d_{i-1} = c_i * i for i >= 1.
   We use 'nth (pred i) ds' to access the derivative coefficient corresponding to index i of xs.
*)
Definition derivative_spec (xs : list Z) (ds : list Z) : Prop :=
  length ds = pred (length xs) /\
  (forall i : nat, (1 <= i < length xs)%nat -> nth (pred i) ds 0 = nth i xs 0 * Z.of_nat i).

Example test_derivative : derivative_spec [0; 7; -1; 0; 0; 0; 0] [7; -2; 0; 0; 0; 0].
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