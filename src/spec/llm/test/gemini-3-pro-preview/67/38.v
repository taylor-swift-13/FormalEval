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

Fixpoint parse_nat_aux (s : string) (acc : nat) : nat :=
  match s with
  | EmptyString => acc
  | String c s' => 
      if is_digit c then parse_nat_aux s' (acc * 10 + (nat_of_ascii c - 48))
      else acc
  end.

Definition string_to_Z (s : string) : Z :=
  match s with
  | EmptyString => 0
  | String c _ => 
      if is_digit c then Z.of_nat (parse_nat_aux s 0) else 0
  end.

Fixpoint split (sep : ascii) (s : string) : list string :=
  match s with
  | EmptyString => [EmptyString]
  | String c s' =>
      if Ascii.eqb c sep then EmptyString :: split sep s'
      else match split sep s' with
           | [] => [String c EmptyString]
           | w :: ws => String c w :: ws
           end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let words := split " " s in
  let amounts := map string_to_Z words in
  let sum := fold_right Z.add 0 amounts in
  n - sum.

Example test_fruit_distribution : fruit_distribution "0 apples and 0 oranges" 1 = 1.
Proof. compute. reflexivity. Qed.