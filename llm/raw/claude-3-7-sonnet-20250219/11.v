
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Definition string_xor_spec (a b result : string) : Prop :=
  String.length a = String.length b /\
  String.length a = String.length result /\
  (forall i : nat, i < String.length a ->
    (nth (String.get 0 a) i (list_of_string a) = true <-> String.get i a = "1") /\
    (nth (String.get 0 b) i (list_of_string b) = true <-> String.get i b = "1") /\
    (String.get i result = "0" \/ String.get i result = "1") /\
    (String.get i result = "1" <->
      xorb (String.get i a = "1") (String.get i b = "1"))).

(* Auxiliary function: list_of_string converts string to list of ascii or bool might be needed.
   This requires defining or assuming a conversion function from string to list of bool or chars.
   Here the core property is expressed logically with respect to index and XOR semantics. *)
