Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Import Nat.

Open Scope string_scope.

(* Helper function to safely convert a 1-character string literal to ascii *)
Definition char_of_str (s : string) : ascii :=
  match s with
  | String c _ => c
  | EmptyString => ascii_of_nat 0
  end.

(*
  Auxiliary definition (returns bool): Check if a character is a digit.
*)
Definition is_digit_bool (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (nat_of_ascii (char_of_str "0") <=? n) && (n <=? nat_of_ascii (char_of_str "9")).

(*
  Auxiliary definition (returns Prop): Check if a character is a latin letter.
*)
Definition is_alpha (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (nat_of_ascii (char_of_str "a") <= n /\ n <= nat_of_ascii (char_of_str "z")) \/
  (nat_of_ascii (char_of_str "A") <= n /\ n <= nat_of_ascii (char_of_str "Z")).

(* Input file name is an arbitrary string, no extra constraints *)
Definition problem_141_pre (file_name : string) : Prop := True.

(* file_name_check function specification *)
Definition problem_141_spec (file_name_str : string) (result : string) : Prop :=
  let file_name := list_ascii_of_string file_name_str in
  let dot := char_of_str "." in
  (* Define a proposition `is_valid` to describe if a file name is valid *)
  let is_valid :=
    (* Condition 1: Number of digits in the file name should not exceed three *)
    (length (filter is_digit_bool file_name) <= 3) /\

    (* Split the file name by the unique '.' into prefix and suffix *)
    (exists prefix suffix,
      file_name = prefix ++ dot :: suffix /\
      ~ In dot (prefix ++ suffix) /\

      (* Condition 2: The part before '.' should not be empty, and it starts with a letter *)
      (exists first_char rest_prefix,
        prefix = first_char :: rest_prefix /\ is_alpha first_char) /\

      (* Condition 3: The part after '.' should be one of "txt", "exe", or "dll" *)
      (suffix = list_ascii_of_string "txt" \/
       suffix = list_ascii_of_string "exe" \/
       suffix = list_ascii_of_string "dll"))
  in
  (* Core specification: if valid, result is "Yes", otherwise "No" *)
  (is_valid /\ result = "Yes") \/
  (~is_valid /\ result = "No").

Example test_problem_141 : problem_141_spec "example.txt" "Yes".
Proof.
  (* Unfold the specification *)
  unfold problem_141_spec.
  
  (* We intend to prove the left branch: (is_valid /\ result = "Yes") *)
  left.
  split.
  
  - (* Part 1: Prove is_valid *)
    split.
    + (* Condition 1: Number of digits <= 3 *)
      (* Simplify and compute the filter on the concrete string "example.txt" *)
      vm_compute. 
      repeat constructor.
      
    + (* Condition 2 & 3: Structure of the filename *)
      exists (list_ascii_of_string "example").
      exists (list_ascii_of_string "txt").
      
      repeat split.
      
      * (* 2a: Reconstruction matches input *)
        simpl. reflexivity.
        
      * (* 2b: No other dots in prefix or suffix *)
        intro H.
        simpl in H.
        (* Destruct the 'In' hypothesis for every character to show contradiction *)
        (* Note: The list is finite, so we can exhaustively destruct *)
        repeat (destruct H as [H | H]; [ discriminate H | ]).
        assumption.
        
      * (* 2c: Prefix is not empty and starts with a letter *)
        exists (char_of_str "e").
        exists (list_ascii_of_string "xample").
        split.
        -- simpl. reflexivity.
        -- (* Prove 'e' is alpha *)
           unfold is_alpha.
           left. (* 'e' is lowercase *)
           simpl.
           split; repeat constructor.
           
      * (* 2d: Suffix is valid ("txt") *)
        left. simpl. reflexivity.

  - (* Part 2: Prove result = "Yes" *)
    reflexivity.
Qed.