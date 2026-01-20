Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* Use string scope for string literals *)
Open Scope string_scope.
(* Use nat scope for arithmetic operations *)
Open Scope nat_scope.

Definition is_lowercase (c : ascii) : bool :=
  let n := nat_of_ascii c in
  andb (97 <=? n) (n <=? 122).

Definition rotate_char (c : ascii) : ascii :=
  if is_lowercase c then
    let n := nat_of_ascii c in
    let shifted := (n - 97 + 4) mod 26 + 97 in
    ascii_of_nat shifted
  else
    c.

Fixpoint encrypt_aux (s : list ascii) : list ascii :=
  match s with
  | [] => []
  | c :: rest => rotate_char c :: encrypt_aux rest
  end.

Definition string_to_list (s : string) : list ascii :=
  list_ascii_of_string s.

Definition list_to_string (l : list ascii) : string :=
  string_of_list_ascii l.

Definition encrypt_spec (s : string) (result : string) : Prop :=
  result = list_to_string (encrypt_aux (string_to_list s)).

Example test_encrypt_hi_lm : encrypt_spec "hi" "lm".
Proof.
  (* Unfold the specification definition *)
  unfold encrypt_spec.
  
  (* 
     Perform computational evaluation. 
     vm_compute is highly efficient for evaluating functions 
     on concrete inputs (like string literals and nats).
     It will execute string_to_list, encrypt_aux, rotate_char, 
     and list_to_string, reducing the term to "lm".
  *)
  vm_compute.
  
  (* The goal is now "lm" = "lm", which is reflexively true. *)
  reflexivity.
Qed.