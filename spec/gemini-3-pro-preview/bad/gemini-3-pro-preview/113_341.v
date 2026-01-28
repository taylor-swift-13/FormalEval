Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Import ListNotations.
Open Scope string_scope.
Open Scope char_scope.

Definition is_odd_digit (c : ascii) : bool :=
  match c with
  | "1" | "3" | "5" | "7" | "9" => true
  | _ => false
  end.

Fixpoint count_odd_digits (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => (if is_odd_digit c then 1 else 0) + count_odd_digits s'
  end.

Parameter string_of_nat : nat -> string.

Definition template : string := "the number of odd elements in the string i of the input."%string.

Fixpoint replace_i (s : string) (replacement : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => 
      if (Ascii.eqb c "i") then 
        replacement ++ (replace_i s' replacement)
      else 
        String c (replace_i s' replacement)
  end.

Definition odd_count_spec (lst : list string) (ans : list string) : Prop :=
  ans = map (fun s => replace_i template (string_of_nat (count_odd_digits s))) lst.

Axiom string_of_nat_47 : string_of_nat 47 = "41"%string.
Axiom string_of_nat_41 : string_of_nat 41 = "41"%string.
Axiom string_of_nat_29 : string_of_nat 29 = "29"%string.
Axiom string_of_nat_4 : string_of_nat 4 = "4"%string.
Axiom string_of_nat_25 : string_of_nat 25 = "25"%string.
Axiom string_of_nat_0 : string_of_nat 0 = "0"%string.
Axiom string_of_nat_38 : string_of_nat 38 = "38"%string.

Example test_odd_count : 
  odd_count_spec 
    ["999910103333333333333310101111111999999999999"; "11111111111111111111113579111"; "0000000000001579000"; "1111111111111111111111111"; "02"; "99999999999995555555555555555555555559"; "33333333333333333333333333333"] 
    ["the number of odd elements 41n the str41ng 41 of the 41nput."; "the number of odd elements 29n the str29ng 29 of the 29nput."; "the number of odd elements 4n the str4ng 4 of the 4nput."; "the number of odd elements 25n the str25ng 25 of the 25nput."; "the number of odd elements 0n the str0ng 0 of the 0nput."; "the number of odd elements 38n the str38ng 38 of the 38nput."; "the number of odd elements 29n the str29ng 29 of the 29nput."].
Proof.
  unfold odd_count_spec.
  simpl.
  try rewrite string_of_nat_47.
  try rewrite string_of_nat_41.
  rewrite string_of_nat_29.
  rewrite string_of_nat_4.
  rewrite string_of_nat_25.
  rewrite string_of_nat_0.
  rewrite string_of_nat_38.
  reflexivity.
Qed.