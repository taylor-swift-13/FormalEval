
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Init.Nat.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope char_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (n >=? 48)%nat && (n <=? 57)%nat.

Fixpoint all_digits (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => is_digit c && all_digits s'
  end.

Definition digit_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint str_to_Z_aux (s : string) (acc : Z) : Z :=
  match s with
  | EmptyString => acc
  | String c s' => str_to_Z_aux s' (acc * 10 + digit_to_Z c)
  end.

Definition str_to_Z (s : string) : Z := str_to_Z_aux s 0.

Definition get_max_days (m : Z) : Z :=
  if m =? 1 then 31
  else if m =? 2 then 29
  else if m =? 3 then 31
  else if m =? 4 then 30
  else if m =? 5 then 31
  else if m =? 6 then 30
  else if m =? 7 then 31
  else if m =? 8 then 31
  else if m =? 9 then 30
  else if m =? 10 then 31
  else if m =? 11 then 30
  else if m =? 12 then 31
  else 0.

Definition valid_date_spec (date : string) (result : bool) : Prop :=
  let len := String.length date in
  let c2 := String.get 2 date in
  let c5 := String.get 5 date in
  let m_str := substring 0 2 date in
  let d_str := substring 3 2 date in
  let y_str := substring 6 4 date in
  
  result = true <->
  (len = 10%nat /\
   c2 = Some "-" /\
   c5 = Some "-" /\
   all_digits m_str = true /\
   all_digits d_str = true /\
   all_digits y_str = true /\
   let m := str_to_Z m_str in
   let d := str_to_Z d_str in
   (1 <= m <= 12) /\
   (1 <= d <= get_max_days m)).
