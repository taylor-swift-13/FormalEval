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

(* Axiom for the behavior of string_of_nat on 0. 
   We use %string because char_scope interprets "0" as an ascii character by default. *)
Axiom string_of_nat_0 : string_of_nat 0 = "0"%string.

Example test_odd_count : 
  odd_count_spec 
    ["2"; "6"; "8"; "2"]%string 
    ["the number of odd elements 0n the str0ng 0 of the 0nput."; 
     "the number of odd elements 0n the str0ng 0 of the 0nput."; 
     "the number of odd elements 0n the str0ng 0 of the 0nput."; 
     "the number of odd elements 0n the str0ng 0 of the 0nput."]%string.
Proof.
  unfold odd_count_spec.
  simpl.
  rewrite string_of_nat_0.
  simpl.
  reflexivity.
Qed.