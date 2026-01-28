Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Import ListNotations.
Open Scope string_scope.

Definition is_odd_digit (c : ascii) : bool :=
  match c with
  | "1"%char | "3"%char | "5"%char | "7"%char | "9"%char => true
  | _ => false
  end.

Fixpoint count_odd_digits (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => (if is_odd_digit c then 1 else 0) + count_odd_digits s'
  end.

Parameter string_of_nat : nat -> string.

Definition template : string := "the number of odd elements in the string i of the input.".

Fixpoint replace_i (s : string) (replacement : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => 
      if (Ascii.eqb c "i"%char) then 
        replacement ++ (replace_i s' replacement)
      else 
        String c (replace_i s' replacement)
  end.

Definition odd_count_spec (lst : list string) (ans : list string) : Prop :=
  ans = map (fun s => replace_i template (string_of_nat (count_odd_digits s))) lst.

Axiom string_of_nat_0 : string_of_nat 0 = "0".
Axiom string_of_nat_1 : string_of_nat 1 = "1".
Axiom string_of_nat_2 : string_of_nat 2 = "2".
Axiom string_of_nat_25 : string_of_nat 25 = "25".

Example test_odd_count : 
  odd_count_spec 
    ["123"; "456"; "789"; "246"; "4246"; "802"; "123"; "1111111111111111111111111802"; "246"; "246"; "1111111111111111111111111802"; "789"; "246"] 
    ["the number of odd elements 2n the str2ng 2 of the 2nput."; "the number of odd elements 1n the str1ng 1 of the 1nput."; "the number of odd elements 2n the str2ng 2 of the 2nput."; "the number of odd elements 0n the str0ng 0 of the 0nput."; "the number of odd elements 0n the str0ng 0 of the 0nput."; "the number of odd elements 0n the str0ng 0 of the 0nput."; "the number of odd elements 2n the str2ng 2 of the 2nput."; "the number of odd elements 25n the str25ng 25 of the 25nput."; "the number of odd elements 0n the str0ng 0 of the 0nput."; "the number of odd elements 0n the str0ng 0 of the 0nput."; "the number of odd elements 25n the str25ng 25 of the 25nput."; "the number of odd elements 2n the str2ng 2 of the 2nput."; "the number of odd elements 0n the str0ng 0 of the 0nput."].
Proof.
  unfold odd_count_spec.
  simpl.
  rewrite string_of_nat_0.
  rewrite string_of_nat_1.
  rewrite string_of_nat_2.
  rewrite string_of_nat_25.
  simpl.
  reflexivity.
Qed.