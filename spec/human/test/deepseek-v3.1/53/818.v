Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_100_neg999999 : 
  problem_53_pre 100 (-999999) -> 
  problem_53_spec 100 (-999999) (-999899).
Proof.
  intro Hpre.
  unfold problem_53_spec.
  reflexivity.
Qed.