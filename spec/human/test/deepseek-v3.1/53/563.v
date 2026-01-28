Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition problem_53_pre (x y : Z) : Prop := True.

Definition problem_53_spec (x : Z) (y : Z) (output : Z) : Prop :=
  output = x + y.

Example test_add_7_neg999999999999999999997 : 
  problem_53_pre 7 (-999999999999999999997) -> 
  problem_53_spec 7 (-999999999999999999997) (-999999999999999999990).
Proof.
  intro Hpre.
  unfold problem_53_spec.
  simpl.
  reflexivity.
Qed.