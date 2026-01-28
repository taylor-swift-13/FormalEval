Require Import List.
Require Import Ascii.
Require Import String.
Require Import Bool.
Require Import Lia.
Import ListNotations.
Open Scope string_scope.

(* Define the specification *)
Definition problem_11_spec (a b output : string) : Prop :=
  String.length a = String.length b /\
  String.length output = String.length a /\
  forall i,
    i < String.length output ->
    (String.get i a = String.get i b -> String.get i output = Some "0"%char) /\
    (String.get i a <> String