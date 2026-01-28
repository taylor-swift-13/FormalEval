Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* is_odd_digit: check if an ascii character represents an odd digit *)
Definition is_odd_digit (c : ascii) : bool :=
  match c with
  | "1"%char | "3"%char | "5"%char | "7"%char | "9"%char => true
  | _ => false
  end.

(* count_odd_digits: count number of odd digits in a string *)
Fixpoint count_odd_digits (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => (if is_odd_digit c then 1 else 0) + count_odd_digits s'
  end.

(* Helper function to convert nat to string (digits in reverse order) *)
Fixpoint nat_to_string_aux (m : nat) : string :=
  match m with
  | 0 => EmptyString
  | S m' => 
      let d := ascii_of_nat (48 + (m mod 10)) in
      String d (nat_to_string_aux (m / 10))
  end.

(* Reverse a string *)
Fixpoint rev_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => (rev_string s') ++ String c EmptyString
  end.

(* Convert nat to string with proper digit order *)
Definition nat_to_string (n : nat) : string :=
  match n with
  | 0 => "0"%string
  | _ => rev_string (nat_to_string_aux n)
  end.

(* replace_char_with_string: replace all occurrences of a target ascii in string with another string *)
Fixpoint replace_char_with_string (target : ascii) (replacement : string) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => 
      if Ascii.eqb c target 
      then replacement ++ replace_char_with_string target replacement s'
      else String c (replace_char_with_string target replacement s')
  end.

(* process a single string: produces the output string with the count embedded *)
Definition process_string (s : string) : string :=
  let cnt := count_odd_digits s in
  let cnt_str := nat_to_string cnt in
  let templ := "the number of odd elements in the string i of the input."%string in
  replace_char_with_string "i"%char cnt_str templ.

(* implementation: for each string in list, process it *)
Definition odd_count_impl (input : list string) : list string :=
  map process_string input.

(* All strings contain only digits *)
Definition problem_113_pre (input : list string) : Prop :=
  Forall (fun s =>
    let fix all_digits (t : string) : Prop :=
      match t with
      | EmptyString => True
      | String ch rest =>
          let n := nat_of_ascii ch in (48 <= n /\ n <= 57) /\ all_digits rest
      end in all_digits s) input.

(* Specification: output matches the implementation *)
Definition problem_113_spec (input : list string) (output : list string) : Prop :=
  output = odd_count_impl input.

(* Test case *)
Example test_single :
  odd_count_impl [ "1234567" ] = [ "the number of odd elements 4n the str4ng 4 of the 4nput." ].
Proof.
  unfold odd_count_impl.
  simpl.
  unfold process_string.
  simpl.
  (* count_odd_digits "1234567" = 4 *)
  (* Let's verify each character: '1'(odd), '2'(even), '3'(odd), '4'(even), '5'(odd), '6'(even), '7'(odd) *)
  (* Total odd digits = 4 *)
  (* Convert 4 to string: "4" *)
  simpl.
  (* Replace "i" with "4" in the template *)
  (* Template: "the number of odd elements in the string i of the input." *)
  (* Replace all 'i' characters with "4" *)
  (* Expected: "the number of odd elements 4n the str4ng 4 of the 4nput." *)
  reflexivity.
Qed.