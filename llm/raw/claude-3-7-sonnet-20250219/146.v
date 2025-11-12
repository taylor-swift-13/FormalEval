
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition odd_digit (c : ascii) : bool :=
  match c with
  | "1"%char => true
  | "3"%char => true
  | "5"%char => true
  | "7"%char => true
  | "9"%char => true
  | _ => false
  end.

Fixpoint string_of_nat (n : nat) : string :=
  match n with
  | 0 => "0"
  | _ =>
    let digits := "0123456789" in
    let rec_strip_leading_zeros := fix f s :=
      match s with
      | EmptyString => EmptyString
      | String "0"%char rest => f rest
      | _ => s
      end
    in
    let rec_build_string := fix f x :=
      match x with
      | 0 => ""
      | _ =>
        let q := x / 10 in
        let r := x mod 10 in
        (f q) ++ String (nth r digits "0"%char) EmptyString
      end
    in
    let s := rec_build_string n in
    if String.length s =? 0 then "0" else s
  end.

Definition first_char (s : string) : option ascii :=
  match s with
  | EmptyString => None
  | String c _ => Some c
  end.

Fixpoint last_char (s : string) : option ascii :=
  match s with
  | EmptyString => None
  | String c EmptyString => Some c
  | String _ rest => last_char rest
  end.

Definition specialFilter_spec (nums : list nat) (result : nat) : Prop :=
  result = 
    length 
      (filter
         (fun num =>
            let s := string_of_nat num in
            (num >? 10) &&
            match first_char s, last_char s with
            | Some fc, Some lc => odd_digit fc && odd_digit lc
            | _, _ => false
            end)
         nums).
