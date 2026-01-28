Require Import Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Import ListNotations.

Fixpoint count_digit_7_aux (k fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S f' =>
    match k with
    | 0 => 0
    | _ =>
      (if Nat.eqb (k mod 10) 7 then 1 else 0) +
      count_digit_7_aux (k / 10) f'
    end
  end.

Definition count_digit_7 (k : nat) : nat :=
  count_digit_7_aux k k.

Definition fizz_buzz_impl (n : nat) : nat :=
  List.fold_left
    (fun acc i =>
      acc +
      (if orb (Nat.eqb (i mod 11) 0) (Nat.eqb (i mod 13) 0) then
         count_digit_7 i
       else
         0))
    (List.seq 0 n)
    0.

Definition problem_36_pre (n : nat) : Prop := True.

Definition problem_36_spec (n : nat) (output : nat) : Prop :=
  output = fizz_buzz_impl n.

Fixpoint fizz_buzz_worker (count start acc : nat) : nat :=
  match count with
  | 0 => acc
  | S c' =>
    let term :=
      if orb (Nat.eqb (start mod 11) 0) (Nat.eqb (start mod 13) 0) then
         count_digit_7 start
       else
         0
    in
    fizz_buzz_worker c' (S start) (acc + term)
  end.

Lemma fizz_buzz_worker_eq : forall count start acc,
  List.fold_left
    (fun acc i =>
      acc +
      (if orb (Nat.eqb (i mod 11) 0) (Nat.eqb (i mod 13) 0) then
         count_digit_7 i
       else
         0))
    (List.seq start count)
    acc = fizz_buzz_worker count start acc.
Proof.
  induction count as [|c IH]; intros start acc.
  - reflexivity.
  - simpl.
    rewrite IH.
    reflexivity.
Qed.

Example test_case_1 : problem_36_spec 123455 9487.
Proof.
  unfold problem_36_spec.
  unfold fizz_buzz_impl.
  rewrite fizz_buzz_worker_eq.
  vm_compute.
  reflexivity.
Qed.