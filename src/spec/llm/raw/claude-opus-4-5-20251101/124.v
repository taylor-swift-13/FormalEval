
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.

Open Scope Z_scope.
Open Scope string_scope.

Definition days_in_month : list Z := [31; 29; 31; 30; 31; 30; 31; 31; 30; 31; 30; 31].

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (48 <=? n)%nat (n <=? 57)%nat.

Definition all_digits (s : string) : bool :=
  forallb is_digit (list_ascii_of_string s).

Definition string_to_nat (s : string) : option nat :=
  if all_digits s then
    Some (fold_left (fun acc c => acc * 10 + (nat_of_ascii c - 48))%nat 
                    (list_ascii_of_string s) 0%nat)
  else None.

Definition nth_Z (l : list Z) (n : nat) : Z :=
  nth n l 0.

Definition valid_date_spec (date : string) (result : bool) : Prop :=
  let len := length (list_ascii_of_string date) in
  (len <> 10%nat -> result = false) /\
  (len = 10%nat ->
    let c2 := nth 2 (list_ascii_of_string date) "000"%char in
    let c5 := nth 5 (list_ascii_of_string date) "000"%char in
    (c2 <> "-"%char \/ c5 <> "-"%char -> result = false) /\
    (c2 = "-"%char /\ c5 = "-"%char ->
      let m_str := substring 0 2 date in
      let d_str := substring 3 2 date in
      let y_str := substring 6 4 date in
      (all_digits m_str = false \/ all_digits d_str = false \/ all_digits y_str = false -> 
        result = false) /\
      (all_digits m_str = true /\ all_digits d_str = true /\ all_digits y_str = true ->
        match string_to_nat m_str, string_to_nat d_str with
        | Some m_nat, Some d_nat =>
          let m := Z.of_nat m_nat in
          let d := Z.of_nat d_nat in
          ((m < 1 \/ m > 12) -> result = false) /\
          (1 <= m <= 12 ->
            let max_days := nth_Z days_in_month (m_nat - 1) in
            ((d < 1 \/ d > max_days) -> result = false) /\
            (1 <= d <= max_days -> result = true))
        | _, _ => result = false
        end))).
