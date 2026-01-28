Require Import Coq.ZArith.ZArith.
Require Import Lia.
Open Scope Z_scope.

(* Definition from specification *)
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

(* Test case proof *)
Example test_case_2 : problem_138_spec 12 true.
Proof.
  unfold problem_138_spec.
  split.
  - intro H.
    exists 2, 2, 2, 6.
    repeat split.
    + unfold is_positive_even. exists 1. lia.
    + unfold is_positive_even. exists 1. lia.
    + unfold is_positive_even. exists 1. lia.
    + unfold is_positive_even. exists 3. lia.
    + reflexivity.
  - intro H.
    reflexivity.
Qed.