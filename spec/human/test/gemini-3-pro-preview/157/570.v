Require Import ZArith.
Require Import Psatz.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop :=   (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example test_problem_157 : problem_157_spec 110 2019 2019 false.
Proof.
  unfold problem_157_spec.
  split.
  - intro H.
    discriminate.
  - intro H.
    lia.
Qed.