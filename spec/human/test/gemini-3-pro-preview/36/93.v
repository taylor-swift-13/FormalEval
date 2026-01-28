Require Import Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool Coq.NArith.NArith.
Import ListNotations.

Fixpoint count_digit_7_aux_N (k : N) (fuel : nat) : N :=
  match fuel with
  | 0 => 0%N
  | S f' =>
    match k with
    | 0%N => 0%N
    | _ =>
      (if (k mod 10 =? 7)%N then 1%N else 0%N) +
      count_digit_7_aux_N (k / 10)%N f'
    end
  end.

Definition count_digit_7 (k : nat) : nat :=
  N.to_nat (count_digit_7_aux_N (N.of_nat k) (N.to_nat (N.size (N.of_nat k)) + 1)).

Definition fizz_buzz_impl (n : nat) : nat :=
  let n_N := N.of_nat n in
  let res :=
    N.iter n_N (fun (acc_i : N * N) =>
      let (acc, i) := acc_i in
      let inc :=
        if (i mod 11 =? 0)%N || (i mod 13 =? 0)%N then
          count_digit_7_aux_N i (N.to_nat (N.size i) + 1)
        else
          0%N in
      (acc + inc, i + 1)%N) (0%N, 0%N)
  in
  N.to_nat (fst res).

Definition problem_36_pre (n : nat) : Prop := True.

Definition problem_36_spec (n : nat) (output : nat) : Prop :=
  output = fizz_buzz_impl n.

Example test_case_1 : problem_36_spec 555554 43688.
Proof.
  unfold problem_36_spec.
  vm_compute.
  reflexivity.
Qed.