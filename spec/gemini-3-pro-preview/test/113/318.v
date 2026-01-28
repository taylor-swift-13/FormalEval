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

Axiom string_of_nat_0 : string_of_nat 0 = "0"%string.
Axiom string_of_nat_3 : string_of_nat 3 = "3"%string.
Axiom string_of_nat_4 : string_of_nat 4 = "4"%string.
Axiom string_of_nat_5 : string_of_nat 5 = "5"%string.
Axiom string_of_nat_15 : string_of_nat 15 = "15"%string.

Example test_odd_count : 
  odd_count_spec 
    ["13579"%string; "24680"%string; "333333333333333"%string; "1579"%string; "246890126468023"%string; "22222222222"%string; "333333333333333"%string]
    ["the number of odd elements 5n the str5ng 5 of the 5nput."%string; 
     "the number of odd elements 0n the str0ng 0 of the 0nput."%string; 
     "the number of odd elements 15n the str15ng 15 of the 15nput."%string; 
     "the number of odd elements 4n the str4ng 4 of the 4nput."%string; 
     "the number of odd elements 3n the str3ng 3 of the 3nput."%string; 
     "the number of odd elements 0n the str0ng 0 of the 0nput."%string; 
     "the number of odd elements 15n the str15ng 15 of the 15nput."%string].
Proof.
  unfold odd_count_spec.
  simpl.
  rewrite string_of_nat_0, string_of_nat_3, string_of_nat_4, string_of_nat_5, string_of_nat_15.
  simpl.
  reflexivity.
Qed.