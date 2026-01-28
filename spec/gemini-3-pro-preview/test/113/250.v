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

(* Axioms for the behavior of string_of_nat on specific values needed for the test case. *)
Axiom string_of_nat_0 : string_of_nat 0 = "0"%string.
Axiom string_of_nat_1 : string_of_nat 1 = "1"%string.
Axiom string_of_nat_4 : string_of_nat 4 = "4"%string.
Axiom string_of_nat_5 : string_of_nat 5 = "5"%string.
Axiom string_of_nat_11 : string_of_nat 11 = "11"%string.
Axiom string_of_nat_25 : string_of_nat 25 = "25"%string.

Example test_odd_count : 
  odd_count_spec 
    ["08002"; "1231123"; "456"; "1101012311230111"; "0802"; "10110100"; "1111111111111111111111111802"; "802"; "1101012311230111"]%string
    ["the number of odd elements 0n the str0ng 0 of the 0nput."; "the number of odd elements 5n the str5ng 5 of the 5nput."; "the number of odd elements 1n the str1ng 1 of the 1nput."; "the number of odd elements 11n the str11ng 11 of the 11nput."; "the number of odd elements 0n the str0ng 0 of the 0nput."; "the number of odd elements 4n the str4ng 4 of the 4nput."; "the number of odd elements 25n the str25ng 25 of the 25nput."; "the number of odd elements 0n the str0ng 0 of the 0nput."; "the number of odd elements 11n the str11ng 11 of the 11nput."]%string.
Proof.
  unfold odd_count_spec.
  simpl.
  rewrite string_of_nat_0, string_of_nat_1, string_of_nat_4, string_of_nat_5, string_of_nat_11, string_of_nat_25.
  simpl.
  reflexivity.
Qed.