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

Fixpoint fizz_buzz_worker (n k acc : nat) : nat :=
  match n with
  | 0 => acc
  | S n' =>
    let term := 
      if orb (Nat.eqb (k mod 11) 0) (Nat.eqb (k mod 13) 0) then
         count_digit_7 k
       else
         0
    in
    fizz_buzz_worker n' (S k) (acc + term)
  end.

Lemma fizz_buzz_equiv_lemma : forall n k acc,
  List.fold_left
    (fun acc i =>
      acc +
      (if orb (Nat.eqb (i mod 11) 0) (Nat.eqb (i mod 13) 0) then
         count_digit_7 i
       else
         0))
    (List.seq k n)
    acc = fizz_buzz_worker n k acc.
Proof.
  induction n as [| n' IH]; intros k acc.
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma fizz_buzz_equiv : forall n,
  fizz_buzz_impl n = fizz_buzz_worker n 0 0.
Proof.
  intros n.
  unfold fizz_buzz_impl.
  apply fizz_buzz_equiv_lemma.
Qed.

Example test_case_2 : problem_36_spec 123454 9487.
Proof.
  unfold problem_36_spec.
  rewrite fizz_buzz_equiv.
  vm_compute.
  reflexivity.
Qed.