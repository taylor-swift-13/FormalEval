
Require Import List.
Require Import String.
Require Import Ascii.

Definition sort_numbers_spec (numbers : string) (sorted_numbers : string) : Prop :=
  let numeral_order := ["zero"; "one"; "two"; "three"; "four"; "five"; "six"; "seven"; "eight"; "nine"] in
  let to_int (s : string) : option nat :=
    match find (fun x => string_dec x s) numeral_order with
    | Some idx => Some (index_of numeral_order idx)
    | None => None
    end
  in
  let str_to_list (s : string) : list string :=
    match s with
    | EmptyString => nil
    | _ => split_string s " "
    end
  in
  let list_to_str (l : list string) : string :=
    match l with
    | nil => EmptyString
    | _ => join_string " " l
    end
  in
  let numbers_list := str_to_list numbers in
  let sorted_list := sort (fun a b => match (to_int a, to_int b) with
                                      | (Some a', Some b') => a' <=? b'
                                      | _ => false
                                      end) numbers_list in
  sorted_numbers = list_to_str sorted_list.
