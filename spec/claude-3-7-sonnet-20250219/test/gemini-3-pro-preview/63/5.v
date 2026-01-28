Require Import Arith.Arith.

Fixpoint fibfib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n1 =>
      match n1 with
      | 0 => 0
      | S n2 =>
          match n2 with
          | 0 => 1
          | S n3 => fibfib n1 + fibfib n2 + fibfib n3
          end
      end
  end.

Definition fibfib_spec (n : nat) (res : nat) : Prop :=
  fibfib n = res.

Example fibfib_test_case : fibfib_spec 10 81.
Proof.
  unfold fibfib_spec.
  reflexivity.
Qed.