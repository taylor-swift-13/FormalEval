Require Import Arith.Arith.

Fixpoint fibfib (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | S p =>
      match p with
      | S q =>
          match q with
          | S r => fibfib p + fibfib q + fibfib r
          | _ => 0
          end
      | _ => 0
      end
  end.

Definition fibfib_spec (n : nat) (res : nat) : Prop :=
  fibfib n = res.

Example fibfib_test_case : fibfib_spec 21 66012.
Proof.
  unfold fibfib_spec.
  reflexivity.
Qed.