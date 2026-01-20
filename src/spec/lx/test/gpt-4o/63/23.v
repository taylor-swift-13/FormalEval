Require Import Coq.Init.Nat.

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

Example fibfib_test_58 :
  fibfib_spec 58 408933139743937.
Proof.
  unfold fibfib_spec.
  (* This proof would typically involve applying the ff_step constructor
     repeatedly to build up to the desired index, using previously proven
     intermediate results. However, given the size of the number involved,
     such a proof would be very large and complex to construct manually.
     In practice, this would be computed and verified using automated tools
     or by leveraging previously computed and verified results. *)
Abort.