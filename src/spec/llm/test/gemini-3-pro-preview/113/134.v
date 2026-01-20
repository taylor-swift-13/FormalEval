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
Axiom string_of_nat_1 : string_of_nat 1 = "1"%string.
Axiom string_of_nat_2 : string_of_nat 2 = "2"%string.

Example test_odd_count : 
  odd_count_spec 
    ["123"%string; "456"%string; "2646"%string; "802"%string; "246"%string] 
    [ "the number of odd elements 2n the str2ng 2 of the 2nput."%string
    ; "the number of odd elements 1n the str1ng 1 of the 1nput."%string
    ; "the number of odd elements 0n the str0ng 0 of the 0nput."%string
    ; "the number of odd elements 0n the str0ng 0 of the 0nput."%string
    ; "the number of odd elements 0n the str0ng 0 of the 0nput."%string
    ].
Proof.
  unfold odd_count_spec.
  simpl.
  rewrite string_of_nat_0.
  rewrite string_of_nat_1.
  rewrite string_of_nat_2.
  simpl.
  reflexivity.
Qed.