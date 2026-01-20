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

Fixpoint parse_nat (s : string) (acc : nat) : nat :=
  match s with
  | EmptyString => acc
  | String c s' =>
      if is_digit c then
        parse_nat s' (acc * 10 + (nat_of_ascii c - 48))
      else acc
  end.

Definition string_to_Z (s : string) : Z :=
  Z.of_nat (parse_nat s 0).

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

Fixpoint split (s : string) : list string :=
  match s with
  | EmptyString => []
  | String c s' =>
      if (c =? " "%char)%char then
        "" :: split s'
      else
        match split s' with
        | [] => [String c EmptyString]
        | w :: ws => (String c w) :: ws
        end
  end.

Fixpoint sum_fruit (words : list string) : Z :=
  match words with
  | [] => 0
  | w :: ws =>
      if is_number_str w then string_to_Z w + sum_fruit ws
      else sum_fruit ws
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  n - sum_fruit (split s).

Example test_fruit_distribution: fruit_distribution "0 apples and 0 oranges" 9 = 9.
Proof. reflexivity. Qed.