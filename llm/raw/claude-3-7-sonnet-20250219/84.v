
Require Import Coq.Strings.String.
Require Import Coq.NArith.BinNat.
Require Import Coq.Lists.List.
Import ListNotations.

Definition digit_sum (n : nat) : nat :=
  let digits := fix digits_aux x :=
    match x with
    | 0 => []
    | _ => (x mod 10) :: digits_aux (x / 10)
    end in
  fold_left Nat.add (digits_aux n) 0.

Definition nat_to_bin_string (n : nat) : string :=
  let fix bin_aux x :=
    match x with
    | 0 => ""
    | _ =>
      let prefix := bin_aux (x / 2) in
      String (if Nat.even x then "0"%char else "1"%char) prefix
    end in
  let s := bin_aux n in
  if s = "" then "0"%string else s.

Definition solve_spec (N : nat) (output : string) : Prop :=
  N <= 10000 /\
  output = nat_to_bin_string (digit_sum N).
