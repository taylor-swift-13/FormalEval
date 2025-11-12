
Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Ascii.
Require Import String.

Open Scope string_scope.

Definition is_odd_digit (c : ascii) : bool :=
  match c with
  | "0"%char => false
  | "1"%char => true
  | "2"%char => false
  | "3"%char => true
  | "4"%char => false
  | "5"%char => true
  | "6"%char => false
  | "7"%char => true
  | "8"%char => false
  | "9"%char => true
  | _ => false
  end.

Fixpoint count_odd_digits (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c cs => (if is_odd_digit c then 1 else 0) + count_odd_digits cs
  end.

Definition replace_i_with_nat (template : string) (n : nat) : string :=
  let n_str := string_of_nat n in
  let fix aux (s : string) : string :=
      match s with
      | EmptyString => EmptyString
      | String c cs =>
        if Ascii.eqb c "i"%char then
          append n_str (aux cs)
        else
          String c (aux cs)
      end
  in aux template.

Definition template_string : string :=
  "the number of odd elements in the string i of the input."%string.

Definition odd_count_spec (lst : list string) (ans : list string) : Prop :=
  length ans = length lst /\
  forall i s o,
    nth_error lst i = Some s ->
    o = count_odd_digits s ->
    nth_error ans i = Some (replace_i_with_nat template_string o).
