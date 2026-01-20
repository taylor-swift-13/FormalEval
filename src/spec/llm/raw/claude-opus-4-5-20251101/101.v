
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

Definition is_separator (c : ascii) : bool :=
  match c with
  | "032"%char => true (* space *)
  | ","%char => true   (* comma *)
  | _ => false
  end.

Definition is_whitespace (c : ascii) : bool :=
  match c with
  | "032"%char => true (* space *)
  | "009"%char => true (* tab *)
  | "010"%char => true (* newline *)
  | "013"%char => true (* carriage return *)
  | _ => false
  end.

Fixpoint split_by_whitespace (s : string) (current : string) (acc : list string) : list string :=
  match s with
  | EmptyString =>
      match current with
      | EmptyString => rev acc
      | _ => rev (current :: acc)
      end
  | String c rest =>
      if is_whitespace c then
        match current with
        | EmptyString => split_by_whitespace rest EmptyString acc
        | _ => split_by_whitespace rest EmptyString (current :: acc)
        end
      else
        split_by_whitespace rest (String c current) acc
  end.

Fixpoint replace_char (s : string) (old_char new_char : ascii) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if Ascii.eqb c old_char then
        String new_char (replace_char rest old_char new_char)
      else
        String c (replace_char rest old_char new_char)
  end.

Definition is_non_empty_string (s : string) : bool :=
  match s with
  | EmptyString => false
  | _ => true
  end.

Definition words_string_spec (s : string) (result : list string) : Prop :=
  let s_replaced := replace_char s ","%char " "%char in
  let words := split_by_whitespace s_replaced EmptyString nil in
  result = filter is_non_empty_string words.
