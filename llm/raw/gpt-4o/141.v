
Require Import String.
Require Import Ascii.
Require Import List.
Import ListNotations.

Definition is_digit (ch : ascii) : bool :=
  match ch with
  | "0"%char | "1"%char | "2"%char | "3"%char | "4"%char
  | "5"%char | "6"%char | "7"%char | "8"%char | "9"%char => true
  | _ => false
  end.

Definition is_alpha (ch : ascii) : bool :=
  match ch with
  | "a"%char | "b"%char | "c"%char | "d"%char | "e"%char
  | "f"%char | "g"%char | "h"%char | "i"%char | "j"%char
  | "k"%char | "l"%char | "m"%char | "n"%char | "o"%char
  | "p"%char | "q"%char | "r"%char | "s"%char | "t"%char
  | "u"%char | "v"%char | "w"%char | "x"%char | "y"%char
  | "z"%char | "A"%char | "B"%char | "C"%char | "D"%char
  | "E"%char | "F"%char | "G"%char | "H"%char | "I"%char
  | "J"%char | "K"%char | "L"%char | "M"%char | "N"%char
  | "O"%char | "P"%char | "Q"%char | "R"%char | "S"%char
  | "T"%char | "U"%char | "V"%char | "W"%char | "X"%char
  | "Y"%char | "Z"%char => true
  | _ => false
  end.

Definition file_name_check_spec (file_name : string) (result : string) : Prop :=
  let digits := filter is_digit (list_ascii_of_string file_name) in
  let f_list := split "." file_name in
  length digits <= 3 /\
  length f_list = 2 /\
  let before_dot := nth 0 f_list "" in
  let after_dot := nth 1 f_list "" in
  before_dot <> "" /\
  is_alpha (hd "?"%char (list_ascii_of_string before_dot)) = true /\
  (after_dot = "txt" \/ after_dot = "exe" \/ after_dot = "dll") /\
  result = "Yes".
