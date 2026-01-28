Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Definition char_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c - 48).

Fixpoint parse_int_aux (s : string) (acc : Z) : Z :=
  match s with
  | EmptyString => acc
  | String c s' => parse_int_aux s' (acc * 10 + char_to_Z c)
  end.

Definition parse_int (s : string) : Z :=
  parse_int_aux s 0.

Fixpoint is_number_str (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c s' =>
      if is_digit c then
        match s' with
        | EmptyString => true
        | _ => is_number_str s'
        end
      else false
  end.

Fixpoint split (s : string) (acc : string) : list string :=
  match s with
  | EmptyString => if string_dec acc "" then [] else [acc]
  | String c s' =>
      if (nat_of_ascii c =? 32)%nat then
        if string_dec acc "" then split s' ""
        else acc :: split s' ""
      else split s' (acc ++ String c EmptyString)
  end.

Fixpoint sum_nums (l : list string) : Z :=
  match l with
  | [] => 0
  | h :: t =>
      if is_number_str h then parse_int h + sum_nums t
      else sum_nums t
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  n - sum_nums (split s "").

Example fruit_distribution_example : fruit_distribution "50 apples and 50 oranges" 103 = 3.
Proof.
  compute. reflexivity.
Qed.