Require Import Reals.
Require Import Psatz.
Open Scope R_scope.

Definition problem_157_pre (a b c : R) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : R) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example test_problem_157 : problem_157_spec 94.48837938393268 26.117120159873124 26.117120159873124 false.
Proof.
  unfold problem_157_spec.
  split.
  - intro H. discriminate.
  - intro H.
    destruct H as [H | [H | H]]; lra.
Qed.