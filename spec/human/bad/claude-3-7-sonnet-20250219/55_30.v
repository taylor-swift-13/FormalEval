Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint fib (n : Z) : Z :=
  match n with
  | 0 => 0
  | 1 => 1
  | Z.pos p => fib (Z.pred n) + fib (Z.pred (Z.pred n))
  | Z.neg _ => 0
  end.

Definition problem_55_pre (n : Z) : Prop := (0 <= n)%Z.

Definition problem_55_spec (n : Z) (res : Z) : Prop :=
  res = fib n.

Example test_fib_66 : problem_55_spec 66 27777890035288.
Proof.
  unfold problem_55_spec.
  simpl.
  reflexivity.
Qed.