Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 > 0 /\ n2 > 0 /\
  ((x1 * n1) mod (x2 * n2) = 0 <-> result = true).

Example test_simplify_597_2975_597_2975 : simplify_spec 597 2975 597 2975 false.
Proof.
  unfold simplify_spec.
  split.
  - lia.
  - split.
    + lia.
    + split.
      * intros H. exfalso.
        compute in H.
        discriminate H.
      * intros H. discriminate H.
Qed.