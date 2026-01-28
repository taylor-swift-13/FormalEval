Require Import Arith.Arith.

Fixpoint fibfib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n0 =>
      match n0 with
      | 0 => 0
      | S n1 =>
          match n1 with
          | 0 => 1
          | S k => fibfib n0 + fibfib n1 + fibfib k
          end
      end
  end.

Definition fibfib_spec (n : nat) (res : nat) : Prop :=
  fibfib n = res.

Example fibfib_test_case : fibfib_spec 12 274.
Proof.
  unfold fibfib_spec.
  reflexivity.
Qed.