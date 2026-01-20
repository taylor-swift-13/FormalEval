Require Import ZArith.
Require Import Bool.
Require Import Lia.

Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 > 0 /\ n2 > 0 /\
  ((x1 * n1) mod (x2 * n2) = 0 <-> result = true).

Example test_simplify_857_2991_857_2991 : simplify_spec 857 2991 857 2991 false.
Proof.
  unfold simplify_spec.
  split.
  - lia.
  - split.
    + lia.
    + split.
      * intros H. exfalso.
        assert (2991 * 2991 = 8946081) as Hdenom by reflexivity.
        assert (857 * 857 = 734449) as Hnumer by reflexivity.
        rewrite Hnumer in H.
        rewrite Hdenom in H.
        compute in H.
        discriminate H.
      * intros H. discriminate H.
Qed.