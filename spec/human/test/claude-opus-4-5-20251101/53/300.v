Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* Pre: no special constraints for `add` *)
Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_10002_10001 : problem_53_spec 10002 10001 20003.
Proof.
  unfold problem_53_spec.
  reflexivity.
Qed.