Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

(* Pre: no special constraints for `add` *)
Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_9999_large : problem_53_spec 9999 123456789098765432101234567891 123456789098765432101234577890.
Proof.
  unfold problem_53_spec.
  reflexivity.
Qed.