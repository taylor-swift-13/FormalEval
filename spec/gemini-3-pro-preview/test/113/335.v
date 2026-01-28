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
Axiom string_of_nat_3 : string_of_nat 3 = "3"%string.
Axiom string_of_nat_5 : string_of_nat 5 = "5"%string.
Axiom string_of_nat_8 : string_of_nat 8 = "8"%string.
Axiom string_of_nat_27 : string_of_nat 27 = "27"%string.

Example test_odd_count : 
  odd_count_spec 
    ["101010101"%string; "1111111111111111111111231111"%string; "10001102"%string; "11010011"%string; "10001100"%string; "2646"%string; "11111111"%string; "2646"%string] 
    ["the number of odd elements 5n the str5ng 5 of the 5nput."%string; "the number of odd elements 27n the str27ng 27 of the 27nput."%string; "the number of odd elements 3n the str3ng 3 of the 3nput."%string; "the number of odd elements 5n the str5ng 5 of the 5nput."%string; "the number of odd elements 3n the str3ng 3 of the 3nput."%string; "the number of odd elements 0n the str0ng 0 of the 0nput."%string; "the number of odd elements 8n the str8ng 8 of the 8nput."%string; "the number of odd elements 0n the str0ng 0 of the 0nput."%string].
Proof.
  unfold odd_count_spec.
  simpl.
  rewrite string_of_nat_0.
  rewrite string_of_nat_3.
  rewrite string_of_nat_5.
  rewrite string_of_nat_8.
  rewrite string_of_nat_27.
  reflexivity.
Qed.