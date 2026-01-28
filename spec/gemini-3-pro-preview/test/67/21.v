Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Definition is_space (c : ascii) : bool :=
  (nat_of_ascii c =? 32)%nat.

Fixpoint parse_int_aux (s : string) (acc : Z) : Z :=
  match s with
  | EmptyString => acc
  | String c s' => 
      if is_digit c 
      then parse_int_aux s' (acc * 10 + (Z.of_nat (nat_of_ascii c) - 48))
      else acc
  end.

Definition parse_int (s : string) : Z := parse_int_aux s 0.

Fixpoint tokens (s : string) (cur : string) : list string :=
  match s with
  | EmptyString => if string_dec cur "" then [] else [cur]
  | String c s' => 
      if is_space c then
        if string_dec cur "" 
        then tokens s' "" 
        else cur :: tokens s' ""
      else tokens s' (cur ++ String c EmptyString)
  end.

Fixpoint sum_fruits (l : list string) : Z :=
  match l with
  | [] => 0
  | h :: t => 
      match h with
      | String c _ => 
          if is_digit c 
          then parse_int h + sum_fruits t
          else sum_fruits t
      | EmptyString => sum_fruits t
      end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  n - sum_fruits (tokens s "").

Example fruit_distribution_example : fruit_distribution "0 apples and 1 oranges" 50 = 49.
Proof. vm_compute. reflexivity. Qed.