Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.
Import ListNotations.

Fixpoint count_digit_7_aux (k : nat) (fuel : nat) {struct fuel} : nat :=
  match fuel with
  | 0 => 0
  | S fuel' =>
      match k with
      | 0 => 0
      | _ => (if Nat.eqb (k mod 10) 7 then 1 else 0) + count_digit_7_aux (k / 10) fuel'
      end
  end.

Definition count_digit_7 (k : nat) : nat :=
  count_digit_7_aux k k.

Definition fizz_buzz_spec (n : nat) (result : nat) : Prop :=
  result =
  List.fold_left
    (fun accumulator i =>
       accumulator + if orb (Nat.eqb (i mod 11) 0) (Nat.eqb (i mod 13) 0) then
                       count_digit_7 i
                     else
                       0)
    (List.seq 0 n)
    0.

Example fizz_buzz_test_50 :
  fizz_buzz_spec 50 0.
Proof.
  unfold fizz_buzz_spec.
  simpl.
  reflexivity.
Qed.