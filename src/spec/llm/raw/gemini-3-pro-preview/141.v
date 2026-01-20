
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.

Open Scope string_scope.
Open Scope char_scope.

Definition is_digit (c : ascii) : bool :=
  (c >=? "0") && (c <=? "9").

Definition is_alpha (c : ascii) : bool :=
  ((c >=? "a") && (c <=? "z")) || ((c >=? "A") && (c <=? "Z")).

Fixpoint count_digits (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => (if is_digit c then 1 else 0) + count_digits s'
  end.

Fixpoint contains_char (s : string) (c : ascii) : bool :=
  match s with
  | EmptyString => false
  | String x s' => (x =? c) || contains_char s' c
  end.

Definition valid_file_name_prop (s : string) : Prop :=
  (count_digits s <= 3) /\
  (exists (prefix suffix : string),
    s = prefix ++ "." ++ suffix /\
    contains_char prefix "." = false /\
    contains_char suffix "." = false /\
    (exists (head : ascii) (tail : string), prefix = String head tail /\ is_alpha head = true) /\
    (suffix = "txt" \/ suffix = "exe" \/ suffix = "dll")).

Definition file_name_check_spec (file_name : string) (result : string) : Prop :=
  (valid_file_name_prop file_name -> result = "Yes") /\
  (~ valid_file_name_prop file_name -> result = "No").
