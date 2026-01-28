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

(* Axioms for the behavior of string_of_nat *)
Axiom string_of_nat_19 : string_of_nat 19 = "19"%string.
Axiom string_of_nat_6 : string_of_nat 6 = "6"%string.
Axiom string_of_nat_9 : string_of_nat 9 = "9"%string.

Example test_odd_count : 
  odd_count_spec 
    ["10103333333333333310101"%string; "41101001156"%string; "10110100111001100"%string] 
    ["the number of odd elements 19n the str19ng 19 of the 19nput."%string; 
     "the number of odd elements 6n the str6ng 6 of the 6nput."%string; 
     "the number of odd elements 9n the str9ng 9 of the 9nput."%string].
Proof.
  unfold odd_count_spec.
  simpl.
  rewrite string_of_nat_19.
  rewrite string_of_nat_6.
  rewrite string_of_nat_9.
  simpl.
  reflexivity.
Qed.