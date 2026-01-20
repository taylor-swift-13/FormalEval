
Require Import String.
Require Import ZArith.
Require Import Lists.List.

Definition days_list : list Z :=
  [31; 29; 31; 30; 31; 30; 31; 31; 30; 31; 30; 31].

Definition valid_date_spec (date : string) (result : bool) : Prop :=
  let length_ok := String.length date =? 10 in
  let dash1_ok := String.get 2 date =? "-" in
  let dash2_ok := String.get 5 date =? "-" in
  let m_str := String.sub date 0 2 in
  let d_str := String.sub date 3 2 in
  let y_str := String.sub date 6 4 in
  let all_digits := 
    (forallb is_digit m_str) && (forallb is_digit d_str) && (forallb is_digit y_str) in
  let m := Z.of_string m_str in
  let d := Z.of_string d_str in
  let month_ok := (1 <=? m) && (m <=? 12) in
  let day_ok := 
    if month_ok 
    then let max_days := nth (Z.to_nat (m - 1)) days_list 0 in
         (1 <=? d) && (d <=? max_days)
    else false in
  result = (length_ok && dash1_ok && dash2_ok && all_digits && month_ok && day_ok).
