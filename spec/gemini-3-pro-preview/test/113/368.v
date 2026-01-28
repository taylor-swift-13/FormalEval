Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Import ListNotations.
Open Scope char_scope.
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
Axiom string_of_nat_4 : string_of_nat 4 = "4".

Example test_odd_count : 
  odd_count_spec 
    ["24000000001"; "0"; "1"; "456"; "8020000000000001579000"; "2446"; "456"; "456"; "456"]
    [ "the number of odd elements 1n the str1ng 1 of the 1nput."
    ; "the number of odd elements 0n the str0ng 0 of the 0nput."
    ; "the number of odd elements 1n the str1ng 1 of the 1nput."
    ; "the number of odd elements 1n the str1ng 1 of the 1nput."
    ; "the number of odd elements 4n the str4ng 4 of the 4nput."
    ; "the number of odd elements 0n the str0ng 0 of the 0nput."
    ; "the number of odd elements 1n the str1ng 1 of the 1nput."
    ; "the number of odd elements 1n the str1ng 1 of the 1nput."
    ; "the number of odd elements 1n the str1ng 1 of the 1nput."
    ].
Proof.
  unfold odd_count_spec.
  simpl.
  repeat rewrite string_of_nat_0.
  repeat rewrite string_of_nat_1.
  repeat rewrite string_of_nat_4.
  simpl.
  reflexivity.
Qed.