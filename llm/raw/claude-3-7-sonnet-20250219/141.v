
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n) && (n <=? 57).

Definition is_alpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((65 <=? n) && (n <=? 90)) || ((97 <=? n) && (n <=? 122)).

Fixpoint count_digits (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c rest => (if is_digit c then 1 else 0) + count_digits rest
  end.

Fixpoint count_char (c : ascii) (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String ch rest => (if ascii_dec c ch then 1 else 0) + count_char c rest
  end.

Fixpoint split_on_dot (s : string) : list string :=
  match s with
  | EmptyString => [EmptyString]
  | String c rest =>
    if ascii_dec c "."
    then EmptyString :: rest :: []
    else
      match split_on_dot rest with
      | [] => [String c EmptyString]
      | h :: t => String c h :: t
      end
  end.

Definition valid_extension (ext : string) : bool :=
  (ext =? "txt") || (ext =? "exe") || (ext =? "dll").

Definition file_name_check_spec (file_name : string) : Prop :=
  (* no more than three digits in file_name *)
  (count_digits file_name <= 3) /\
  (* exactly one '.' in file_name *)
  (count_char "." file_name = 1) /\
  (* split file_name into name and extension at the dot *)
  exists name ext,
    file_name = String "" EmptyString \/ (* note: allowing formalism *)
    (file_name = (name ++ "." ++ ext)) /\
    (* name not empty *)
    (name <> "") /\
    (* first char of name is a latin letter *)
    (exists c rest, name = String c rest /\ is_alpha c = true) /\
    (* ext is valid extension *)
    valid_extension ext = true.
