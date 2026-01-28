Require Import List Ascii String.
Import ListNotations.
Open Scope string_scope.

(* Pre: no special constraints for `same_chars` *)
Definition problem_54_pre (s0 s1 : string) : Prop := True.

Definition problem_54_spec (s0 s1 : string) (b : bool) : Prop :=
  let list_s0 := list_ascii_of_string s0 in
  let list_s1 := list_ascii_of_string s1 in
  b = true <-> (forall (c : ascii), In c list_s0 <-> In c list_s1).

Example test_problem_54 : problem_54_spec "abecde" "abecde" true.
Proof.
  (* Unfold the specification *)
  unfold problem_54_spec.
  (* Simplify string to list conversions *)
  simpl.
  (* Split the bi-implication: b=true <-> (forall c, ...) *)
  split.
  - (* Left to Right: true = true -> forall c, ... *)
    intros _.
    intros c.
    split; intros H.
    + (* Forward direction: In c (s0 chars) -> In c (s1 chars) *)
      (* Decompose the hypothesis H (In c s0) which is a disjunction of equalities *)
      repeat (destruct H as [H | H]; [ 
        (* For each character in s0, substitute it and check if it is in s1 *)
        subst; simpl; tauto 
      | ]).
      (* Handle the base case (In c []) which is False *)
      destruct H.
    + (* Backward direction: In c (s1 chars) -> In c (s0 chars) *)
      (* Decompose the hypothesis H (In c s1) *)
      repeat (destruct H as [H | H]; [ 
        (* For each character in s1, substitute it and check if it is in s0 *)
        subst; simpl; tauto 
      | ]).
      (* Handle the base case *)
      destruct H.
  - (* Right to Left: (forall c, ...) -> true = true *)
    intros _.
    reflexivity.
Qed.