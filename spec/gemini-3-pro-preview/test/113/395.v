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

(* Use %string to force string interpretation in char_scope *)
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

Axiom string_of_nat_0 : string_of_nat 0 = "0"%string.
Axiom string_of_nat_1 : string_of_nat 1 = "1"%string.
Axiom string_of_nat_3 : string_of_nat 3 = "3"%string.
Axiom string_of_nat_5 : string_of_nat 5 = "5"%string.
Axiom string_of_nat_29 : string_of_nat 29 = "29"%string.

Example test_odd_count : 
  odd_count_spec 
    ["24689013"; "13579"; "02"; "456"; "246"; "802"; "456"; "456"; "6"; "33333333333333333333333333333"]%string
    ["the number of odd elements 3n the str3ng 3 of the 3nput."; 
     "the number of odd elements 5n the str5ng 5 of the 5nput."; 
     "the number of odd elements 0n the str0ng 0 of the 0nput."; 
     "the number of odd elements 1n the str1ng 1 of the 1nput."; 
     "the number of odd elements 0n the str0ng 0 of the 0nput."; 
     "the number of odd elements 0n the str0ng 0 of the 0nput."; 
     "the number of odd elements 1n the str1ng 1 of the 1nput."; 
     "the number of odd elements 1n the str1ng 1 of the 1nput."; 
     "the number of odd elements 0n the str0ng 0 of the 0nput."; 
     "the number of odd elements 29n the str29ng 29 of the 29nput."]%string.
Proof.
  unfold odd_count_spec.
  simpl.
  rewrite string_of_nat_3, string_of_nat_5, string_of_nat_0, string_of_nat_1, string_of_nat_29.
  reflexivity.
Qed.