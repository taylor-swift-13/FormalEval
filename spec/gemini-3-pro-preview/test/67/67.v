Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition is_digit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <=? n)%nat && (n <=? 57)%nat.

Fixpoint parse_ints (s : string) (curr : option Z) (acc : list Z) : list Z :=
  match s with
  | EmptyString => 
      match curr with 
      | Some n => n :: acc 
      | None => acc 
      end
  | String c rest =>
      if is_digit c then
        let d := Z.of_nat (nat_of_ascii c - 48) in
        match curr with
        | Some n => parse_ints rest (Some (n * 10 + d)) acc
        | None => parse_ints rest (Some d) acc
        end
      else
        match curr with
        | Some n => parse_ints rest None (n :: acc)
        | None => parse_ints rest None acc
        end
  end.

Definition fruit_distribution (s : string) (n : Z) : Z :=
  let nums := parse_ints s None [] in
  n - fold_right Z.add 0 nums.

Example test_fruit_distribution: fruit_distribution "5 apples and 5 oranges" 13 = 3.
Proof.
  compute. reflexivity.
Qed.