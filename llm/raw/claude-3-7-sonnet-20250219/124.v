
Require Import Coq.Strings.String.
Require Import Coq.Init.Nat.

Definition valid_date_spec (date : string) (result : bool) : Prop :=
  let days := [31; 29; 31; 30; 31; 30; 31; 31; 30; 31; 30; 31] in
  result = true <->
  ( String.length date = 10 /\
    String.get 2 date = Some "-" /\
    String.get 5 date = Some "-" /\
    (forall i, (i = 0 \/ i = 1 \/ i = 3 \/ i = 4 \/ i >= 6) -> 
        Ascii.is_digit (String.get i date) = true) /\
    let m_str := String.substring 0 2 date in
    let d_str := String.substring 3 2 date in
    let y_str := String.substring 6 4 date in
    let m := match Nat_of_string m_str with
             | Some n => n | None => 0 end in
    let d := match Nat_of_string d_str with
             | Some n => n | None => 0 end in
    1 <= m <= 12 /\
    let max_days := nth (m - 1) days 0 in
    1 <= d <= max_days /\
    (forall c, In c (list_of_string y_str) -> Ascii.is_digit c = true)
  ).
