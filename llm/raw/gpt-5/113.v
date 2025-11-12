Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

Local Open Scope string_scope.

Definition i_char : ascii := Ascii.ascii_of_nat 105.

Definition is_digitb (ch : ascii) : bool :=
  let n := nat_of_ascii ch in (48 <=? n) && (n <=? 57).

Definition digit_value (ch : ascii) : nat := nat_of_ascii ch - 48.

Definition odd_digitb (ch : ascii) : bool :=
  is_digitb ch && Nat.odd (digit_value ch).

Fixpoint count_odd_digits (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String ch rest =>
      if odd_digitb ch then S (count_odd_digits rest)
      else count_odd_digits rest
  end.

Definition ascii_of_digit (d : nat) : ascii := Ascii.ascii_of_nat (48 + d).

Fixpoint nat_to_string_aux (n : nat) : string :=
  if n <? 10 then String (ascii_of_digit n) EmptyString
  else nat_to_string_aux (Nat.div n 10) ++ String (ascii_of_digit (Nat.modulo n 10)) EmptyString.

Definition nat_to_string (n : nat) : string :=
  if n =? 0 then "0" else nat_to_string_aux n.

Fixpoint replace_char (s : string) (c : ascii) (r : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String ch rest =>
      if Ascii.eqb ch c
      then r ++ replace_char rest c r
      else String ch (replace_char rest c r)
  end.

Definition template : string := "the number of odd elements in the string i of the input.".

Fixpoint all_digits_string (s : string) : Prop :=
  match s with
  | EmptyString => True
  | String ch rest =>
      (48 <= nat_of_ascii ch)%nat /\ (nat_of_ascii ch <= 57)%nat /\ all_digits_string rest
  end.

Definition odd_count_spec (lst : list string) (ans : list string) : Prop :=
  Forall all_digits_string lst /\
  ans = List.map (fun s => replace_char template i_char (nat_to_string (count_odd_digits s))) lst.