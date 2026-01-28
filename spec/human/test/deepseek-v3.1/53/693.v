Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_4_minus1000000000000000000000 : 
  problem_53_pre 4 (-1000000000000000000000) -> 
  problem_53_spec 4 (-1000000000000000000000) (-999999999999999999996).
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.