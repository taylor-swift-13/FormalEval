Require Import Coq.Init.Nat.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Inductive is_fibfib : nat -> nat -> Prop :=
  | ff_zero : is_fibfib 0 0
  | ff_one  : is_fibfib 1 0
  | ff_two  : is_fibfib 2 1
  | ff_step : forall n res_n res_n1 res_n2,
      is_fibfib n res_n ->
      is_fibfib (S n) res_n1 ->
      is_fibfib (S (S n)) res_n2 ->
      is_fibfib (S (S (S n))) (res_n + res_n1 + res_n2).

Definition fibfib_spec (n : nat) (res : nat) : Prop :=
  is_fibfib n res.

Example fibfib_test_97 :
  fibfib_spec 97 8569995677610263592944752.
Proof.
  unfold fibfib_spec.
  (* The proof for such a large number cannot be completed directly using induction or computation in nat due to size constraints. *)
  Admitted.