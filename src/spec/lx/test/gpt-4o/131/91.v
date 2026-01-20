Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Fixpoint get_digits_helper (n : nat) (fuel : nat) : list nat :=
  match fuel with
  | 0 => []
  | S fuel' =>
      match n with
      | 0 => []
      | _ => (Nat.modulo n 10) :: get_digits_helper (Nat.div n 10) fuel'
      end
  end.

Definition get_digits (n : nat) : list nat :=
  get_digits_helper n n.

Fixpoint product (l : list nat) : nat :=
  match l with
  | [] => 1
  | h :: t => h * product t
  end.

Definition digits_spec (n : nat) (z : nat) : Prop :=
  let all_digits := get_digits n in
  let odd_digits := filter Nat.odd all_digits in
  match odd_digits with
  | [] => z = 0
  | _ => z = product odd_digits
  end.

Example digits_test_43 :
  digits_spec 43 3.
Proof.
  unfold digits_spec.
  simpl.
  reflexivity.
Qed.