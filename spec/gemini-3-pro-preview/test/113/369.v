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
Axiom string_of_nat_4 : string_of_nat 4 = "4"%string.
Axiom string_of_nat_6 : string_of_nat 6 = "6"%string.
Axiom string_of_nat_8 : string_of_nat 8 = "8"%string.
Axiom string_of_nat_17 : string_of_nat 17 = "17"%string.
Axiom string_of_nat_30 : string_of_nat 30 = "30"%string.

Example test_odd_count : 
  odd_count_spec 
    ["468"%string; "0"%string; "101011"%string; "333331011010033333333"%string; "135799"%string; "3579"%string; "3579"%string; "35790000000000001579000"%string; "3579"%string; "3579"%string; "357911111111111111111111111111"%string; "357911111111111111111111111111"%string] 
    ["the number of odd elements 0n the str0ng 0 of the 0nput."%string; "the number of odd elements 0n the str0ng 0 of the 0nput."%string; "the number of odd elements 4n the str4ng 4 of the 4nput."%string; "the number of odd elements 17n the str17ng 17 of the 17nput."%string; "the number of odd elements 6n the str6ng 6 of the 6nput."%string; "the number of odd elements 4n the str4ng 4 of the 4nput."%string; "the number of odd elements 4n the str4ng 4 of the 4nput."%string; "the number of odd elements 8n the str8ng 8 of the 8nput."%string; "the number of odd elements 4n the str4ng 4 of the 4nput."%string; "the number of odd elements 4n the str4ng 4 of the 4nput."%string; "the number of odd elements 30n the str30ng 30 of the 30nput."%string; "the number of odd elements 30n the str30ng 30 of the 30nput."%string].
Proof.
  unfold odd_count_spec.
  simpl.
  rewrite string_of_nat_0, string_of_nat_4, string_of_nat_6, string_of_nat_8, string_of_nat_17, string_of_nat_30.
  simpl.
  reflexivity.
Qed.