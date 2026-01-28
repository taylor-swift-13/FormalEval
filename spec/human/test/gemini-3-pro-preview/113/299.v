Require Import Coq.Strings.String Coq.Lists.List Coq.Strings.Ascii Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope string_scope.
Open Scope nat_scope.

Definition is_odd_digit (c : ascii) : bool :=
  match c with "1"%char|"3"%char|"5"%char|"7"%char|"9"%char => true | _ => false end.

Fixpoint count_odd_digits (s : string) : nat :=
  match s with EmptyString => 0 | String c s' => (if is_odd_digit c then 1 else 0) + count_odd_digits s' end.

(* Helper function to convert nat to string. 
   Uses a fuel argument to satisfy Coq's termination checker for the division recursion. *)
Fixpoint nat_to_string_aux (fuel : nat) (n : nat) : string :=
  match fuel with
  | 0 => EmptyString
  | S fuel' =>
    match n with
    | 0 => EmptyString
    | _ => String (ascii_of_nat (48 + (n mod 10))) (nat_to_string_aux fuel' (n / 10))
    end
  end.

(* Helper to reverse a string *)
Fixpoint rev_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => (rev_string s') ++ String c EmptyString
  end.

Definition nat_to_string (n : nat) : string :=
  match n with
  | 0 => "0"%string
  | _ => rev_string (nat_to_string_aux (S n) n)
  end.

Fixpoint replace_char_with_string (target : ascii) (replacement : string) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => let rest := replace_char_with_string target replacement s' in
                   if Ascii.eqb c target then replacement ++ rest else String c rest
  end.

Definition process_string (s : string) : string :=
  let cnt := count_odd_digits s in
  let cnt_str := nat_to_string cnt in
  let templ := "the number of odd elements in the string i of the input."%string in
  replace_char_with_string "i"%char cnt_str templ.

Definition odd_count_impl (input : list string) : list string := map process_string input.

(* Each string contains only digit characters *)
Definition problem_113_pre (input : list string) : Prop :=
  Forall (fun s =>
    let fix all_digits (t : string) : Prop :=
      match t with
      | EmptyString => True
      | String ch rest =>
          let n := nat_of_ascii ch in (48 <= n /\ n <= 57) /\ all_digits rest
      end in all_digits s) input.

Definition problem_113_spec (input : list string) (output : list string) : Prop :=
  output = odd_count_impl input.

Example problem_113_test :
  problem_113_spec 
    ["12345690"; "13579"; "24680"; "11111"; "22222222222"; "333333333333333"; "1234567890"] 
    ["the number of odd elements 4n the str4ng 4 of the 4nput."; "the number of odd elements 5n the str5ng 5 of the 5nput."; "the number of odd elements 0n the str0ng 0 of the 0nput."; "the number of odd elements 5n the str5ng 5 of the 5nput."; "the number of odd elements 0n the str0ng 0 of the 0nput."; "the number of odd elements 15n the str15ng 15 of the 15nput."; "the number of odd elements 5n the str5ng 5 of the 5nput."].
Proof.
  unfold problem_113_spec.
  unfold odd_count_impl.
  simpl.
  reflexivity.
Qed.