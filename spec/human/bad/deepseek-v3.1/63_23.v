Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Nat.

Open Scope Z_scope.

Fixpoint fibfib (n : Z) : Z :=
  match n with
  | 0 => 0
  | Z.pos p =>
    match Z.to_nat p with
    | O => 0
    | S n' =>
      match Z.to_nat p - 1 with
      | 0 => 0
      | S n'' =>
        match Z.to_nat p - 2 with
        | 0 => 1
        | S n''' => fibfib (Z.of_nat n') + fibfib (Z.of_nat n' - 1) + fibfib (Z.of_nat n' - 2)
        end
      end
    end
  | Z.neg _ => 0
  end.

Definition problem_63_spec (n : Z) (res : Z) : Prop :=
  res = fibfib n.

Example fibfib_test_58 : problem_63_spec 58 408933139743937.
Proof.
  unfold problem_63_spec.
  simpl.
  reflexivity.
Qed.