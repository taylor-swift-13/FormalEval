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

Fixpoint parse_nat (s : string) (acc : nat) : option nat :=
  match s with
  | EmptyString => Some acc
  | String c s' =>
      if is_digit c then
        parse_nat s' (10 * acc + (nat_of_ascii c - 48))
      else None
  end.

Definition Z_of_string_opt (s : string) : option Z :=
  match s with
  | EmptyString => None
  | _ =>
      match parse_nat s 0 with
      | Some n => Some (Z.of_nat n)
      | None => None
      end
  end.

Fixpoint split_aux (s : string) (curr : string) : list string :=
  match s with
  | EmptyString => [curr]
  | String c s' =>
      if (nat_of_ascii c =? 32)%nat then
        curr :: split_aux s' ""
      else
        split_aux s' (curr ++ String c EmptyString)
  end.

Definition split (s : string) : list string :=
  split_aux s "".

Fixpoint filter_map {A B} (f : A -> option B) (l : list A) : list B :=
  match l with
  | [] => []
  | x :: xs =>
      match f x with
      | Some y => y :: filter_map f xs
      | None => filter_map f xs
      end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let words := split s in
  let nums := filter_map Z_of_string_opt words in
  let sum := fold_right Z.add 0 nums in
  n - sum.

Example test_fruit_distribution : fruit_distribution "2 apples and 0 oranges" 3 = 1.
Proof. reflexivity. Qed.