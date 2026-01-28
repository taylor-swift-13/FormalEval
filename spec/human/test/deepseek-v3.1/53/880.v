Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_1000000000000000000000_1000001 : 
  problem_53_pre 1000000000000000000000 1000001 -> 
  problem_53_spec 1000000000000000000000 1000001 1000000000000001000001.
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.