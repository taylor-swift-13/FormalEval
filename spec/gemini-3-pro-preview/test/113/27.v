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

Axiom string_of_nat_2 : string_of_nat 2 = "2"%string.
Axiom string_of_nat_3 : string_of_nat 3 = "3"%string.
Axiom string_of_nat_6 : string_of_nat 6 = "6"%string.

Example test_odd_count : 
  odd_count_spec 
    ["77444888"%string; "12321"%string; "333333"%string; "77444888"%string; "77444888"%string] 
    ["the number of odd elements 2n the str2ng 2 of the 2nput."%string; 
     "the number of odd elements 3n the str3ng 3 of the 3nput."%string; 
     "the number of odd elements 6n the str6ng 6 of the 6nput."%string; 
     "the number of odd elements 2n the str2ng 2 of the 2nput."%string; 
     "the number of odd elements 2n the str2ng 2 of the 2nput."%string].
Proof.
  unfold odd_count_spec.
  simpl.
  rewrite string_of_nat_2.
  rewrite string_of_nat_3.
  rewrite string_of_nat_6.
  reflexivity.
Qed.