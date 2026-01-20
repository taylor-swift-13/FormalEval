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

Example fibfib_test_99 :
  fibfib_spec 99
    (of_num_uint
       (Number.UIntDecimal
          (Decimal.D2
             (Decimal.D8
                (Decimal.D9
                   (Decimal.D9
                      (Decimal.D2
                         (Decimal.D0
                            (Decimal.D8
                               (Decimal.D7
                                  (Decimal.D7
                                     (Decimal.D0
                                        (Decimal.D8
                                           (Decimal.D4
                                              (Decimal.D1
                                                 (Decimal.D6
                                                 (Decimal.D7
                                                 (Decimal.D1
                                                 (Decimal.D7
                                                 (Decimal.D6
                                                 (Decimal.D1
                                                 (Decimal.D2
                                                 (Decimal.D9
                                                 (Decimal.D3
                                                 (Decimal.D4
                                                 (Decimal.D4
                                                 (Decimal.D1
                                                 (Decimal.D7 Decimal.Nil)))))))))))))))))))))))))))).
Proof.
  unfold fibfib_spec.
  (* The proof for such a large number requires external computation or specialized tactics,
     which are not feasible directly in this context. *)
Abort.