
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Open Scope string_scope.

Definition dash : ascii := "-"%char.

Definition is_digit (a : ascii) : Prop :=
  nat_of_ascii "0"%char <= nat_of_ascii a <= nat_of_ascii "9"%char.

Definition digit_val (a : ascii) : nat :=
  Nat.sub (nat_of_ascii a) (nat_of_ascii "0"%char).

Definition parse_decimal_list (l : list ascii) : nat :=
  List.fold_left (fun acc c => acc * 10 + digit_val c) l 0.

Definition day_limit (m : nat) : nat :=
  match m with
  | 1 => 31
  | 2 => 29
  | 3 => 31
  | 4 => 30
  | 5 => 31
  | 6 => 30
  | 7 => 31
  | 8 => 31
  | 9 => 30
  | 10 => 31
  | 11 => 30
  | 12 => 31
  | _ => 0
  end.

Definition valid_date_property (date : string) : Prop :=
  let l := list_of_string date in
  List.length l = 10 /\
  List.nth_error l 2 = Some dash /\
  List.nth_error l 5 = Some dash /\
  let mlist := firstn 2 l in
  let dlist := firstn 2 (skipn 3 l) in
  let ylist := skipn 6 l in
  Forall is_digit mlist /\
  Forall is_digit dlist /\
  Forall is_digit ylist /\
  let m := parse_decimal_list mlist in
  let d := parse_decimal_list dlist in
  1 <= m /\ m <= 12 /\
  1 <= d /\ d <= day_limit m.

Definition valid_date_spec (date : string) (b : bool) : Prop :=
  b = true <-> valid_date_property date.
