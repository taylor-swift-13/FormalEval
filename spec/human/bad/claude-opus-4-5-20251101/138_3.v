Require Import Coq.ZArith.ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition is_positive_even (e : Z) : Prop :=
  exists k : Z, e = 2 * k /\ (k > 0)%Z.

Definition problem_138_pre (n : Z) : Prop := True.

Definition problem_138_spec (n : Z) (b : bool) : Prop :=
  b = true <-> exists e1 e2 e3 e4 : Z,
    is_positive_even e1 /\
    is_positive_even e2 /\
    is_positive_even e3 /\
    is_positive_even e4 /\
    n = e1 + e2 + e3 + e4.

Example test_is_equal_to_sum_even_8 : problem_138_spec 8 true.
Proof.
  unfold problem_138_spec.
  split.
  - intro H.
    exists 2, 2, 2, 2.
    unfold is_positive_even.
    repeat split.
    + exists 1. lia.
    + exists 1. lia.
    + exists 1. lia.
    + exists 1. lia.
    + lia.
  - intro H. reflexivity.
Qed.