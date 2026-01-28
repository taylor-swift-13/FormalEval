Require Import ZArith.
Open Scope Z_scope.

Definition problem_157_pre (a b c : Z) : Prop := (a > 0 /\ b > 0 /\ c > 0).

Definition problem_157_spec (a b c : Z) (res : bool) : Prop :=
  res = true <-> (a * a + b * b = c * c \/
                  a * a + c * c = b * b \/
                  b * b + c * c = a * a).

Example test_3_4_5 :
  problem_157_spec 3 4 5 true.
Proof.
  unfold problem_157_spec.
  split.
  - (* res = true -> right angle condition *)
    intros H.
    rewrite H.
    left.
    reflexivity.
  - (* right angle condition -> res = true *)
    intros H.
    (* We just need to show true = true *)
    (* since res = true is goal *)
    (* The spec states res = true <-> condition *)
    reflexivity.
Qed.