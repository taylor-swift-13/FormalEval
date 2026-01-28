Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

(* Helper function to check if a character is a vowel *)
Definition is_vowel (c : ascii) : bool :=
  match c with
  | "a"%char | "e"%char | "i"%char | "o"%char | "u"%char => true
  | "A"%char | "E"%char | "I"%char | "O"%char | "U"%char => true
  | _ => false
  end.

(* Helper function to swap the case of a letter *)
Definition swap_case (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if andb (leb 65 n) (leb n 90) (* Uppercase? *)
  then ascii_of_nat (n + 32) (* Convert to lowercase *)
  else if andb (leb 97 n) (leb n 122) (* Lowercase? *)
  then ascii_of_nat (n - 32) (* Convert to uppercase *)
  else c. (* Not a letter, remain unchanged *)

(* Helper function to replace a vowel with the letter 2 places ahead *)
Definition replace_vowel (c : ascii) : ascii :=
  match c with
  | "a"%char => "c"%char | "e"%char => "g"%char | "i"%char => "k"%char | "o"%char => "q"%char | "u"%char => "w"%char
  | "A"%char => "C"%char | "E"%char => "G"%char | "I"%char => "K"%char | "O"%char => "Q"%char | "U"%char => "W"%char
  | _ => c
  end.

(* Specification for encoding a single character *)
Definition encode_char_spec (c_in c_out : ascii) : Prop :=
  let c_swapped := swap_case c_in in
  if is_vowel c_in
  then c_out = replace_vowel c_swapped
  else c_out = c_swapped.

(* Precondition: the message contains only letters or spaces *)
Definition problem_93_pre (s_in : string) : Prop :=
  let l_in := list_ascii_of_string s_in in
  Forall (fun c => let n := nat_of_ascii c in (65 <= n /\ n <= 90) \/ (97 <= n /\ n <= 122) \/ n = 32) l_in.

(* Specification for the complete encode function *)
Definition problem_93_spec (s_in s_out : string) : Prop :=
  let l_in := list_ascii_of_string s_in in
  let l_out := list_ascii_of_string s_out in
  Forall2 encode_char_spec l_in l_out.

(* The encode function *)
Fixpoint encode (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c cs =>
      let c_swapped := swap_case c in
      let c_encoded :=
          if is_vowel c
          then replace_vowel c_swapped
          else c_swapped in
      String c_encoded (encode cs)
  end.

(* Test case: input = "TEST", output = "tgst" *)
Example test_encode : encode "TEST" = "tgst".
Proof.
  unfold encode.
  simpl.
  unfold swap_case.
  unfold is_vowel.
  unfold replace_vowel.
  simpl.
  reflexivity.
Qed.