Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_1000001_neg2 : 
  problem_53_pre 1000001 (-2) -> 
  problem_53_spec 1000001 (-2) 999999.
Proof.
  intros _.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.