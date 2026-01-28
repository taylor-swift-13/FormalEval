Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* Pre: no special constraints for `add` *)
Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_large : problem_53_spec 98765432101234567890123456790 (-9999) 98765432101234567890123446791.
Proof.
  unfold problem_53_spec.
  reflexivity.
Qed.