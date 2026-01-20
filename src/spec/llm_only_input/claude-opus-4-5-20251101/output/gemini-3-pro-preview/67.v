Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Definition int := Z.

(* Abstracting Python's string splitting and integer conversion *)
Parameter split : string -> string -> list string.
Parameter to_int : string -> int.

Definition fruit_distribution_spec (s : string) (n : int) (res : int) : Prop :=
  let words := split s " " in
  let c1 := to_int (nth 0 words "") in
  let c2 := to_int (nth 3 words "") in
  n - c1 - c2 >= 0 /\ res = n - c1 - c2.

(* Axioms for the specific test case *)
Axiom split_test : split "5 apples and 6 oranges" " " = ["5"; "apples"; "and"; "6"; "oranges"].
Axiom to_int_5 : to_int "5" = 5.
Axiom to_int_6 : to_int "6" = 6.

Example fruit_distribution_test : fruit_distribution_spec "5 apples and 6 oranges" 19 8.
Proof.
  unfold fruit_distribution_spec.
  rewrite split_test.
  simpl.
  rewrite to_int_5.
  rewrite to_int_6.
  split.
  - unfold Z.ge. intro H. discriminate H.
  - reflexivity.
Qed.