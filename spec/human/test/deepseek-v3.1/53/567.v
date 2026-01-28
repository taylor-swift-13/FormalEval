Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_1000002_neg999999999999999999999 : 
  problem_53_pre 1000002 (-999999999999999999999) -> 
  problem_53_spec 1000002 (-999999999999999999999) (-999999999999998999997).
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.