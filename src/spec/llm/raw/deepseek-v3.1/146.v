
Require Import ZArith.
Require Import String.
Require Import List.
Import ListNotations.

Definition is_odd_digit (d : ascii) : bool :=
  match d with
  | "1" | "3" | "5" | "7" | "9" => true
  | _ => false
  end.

Fixpoint string_of_nat_aux (n : nat) (acc : string) : string :=
  match n with
  | O => acc
  | S n' => string_of_nat_aux n' (String (ascii_of_nat (n mod 10)) acc)
  end.

Definition string_of_nat (n : nat) : string :=
  match n with
  | O => "0"
  | _ => string_of_nat_aux n ""
  end.

Definition specialFilter_spec (nums : list Z) (result : nat) : Prop :=
  result = length (filter (fun num =>
    (num > 10) &&
    (match string_of_nat (Z.to_nat (Z.abs num)) with
     | "" => false
     | s => is_odd_digit (String.get 0 s) && is_odd_digit (String.get (String.length s - 1) s)
     end)) nums).
