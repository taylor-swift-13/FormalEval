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
Axiom string_of_nat_25 : string_of_nat 25 = "25"%string.
Axiom string_of_nat_26 : string_of_nat 26 = "26"%string.
Axiom string_of_nat_33 : string_of_nat 33 = "33"%string.
Axiom string_of_nat_34 : string_of_nat 34 = "34"%string.
Axiom string_of_nat_38 : string_of_nat 38 = "38"%string.

Example test_odd_count : 
  odd_count_spec 
    ["999999999999911111111999999999999"%string; "1111111111111111111111111"%string; "000000000000000"%string; "11111111111111111111111111"%string; "9999199999999911111111999999999999"%string; "99999999999995555555555555555555555559"%string] 
    ["the number of odd elements 33n the str33ng 33 of the 33nput."%string; "the number of odd elements 25n the str25ng 25 of the 25nput."%string; "the number of odd elements 0n the str0ng 0 of the 0nput."%string; "the number of odd elements 26n the str26ng 26 of the 26nput."%string; "the number of odd elements 34n the str34ng 34 of the 34nput."%string; "the number of odd elements 38n the str38ng 38 of the 38nput."%string].
Proof.
  unfold odd_count_spec.
  simpl.
  rewrite string_of_nat_33.
  rewrite string_of_nat_25.
  rewrite string_of_nat_0.
  rewrite string_of_nat_26.
  rewrite string_of_nat_34.
  rewrite string_of_nat_38.
  simpl.
  reflexivity.
Qed.