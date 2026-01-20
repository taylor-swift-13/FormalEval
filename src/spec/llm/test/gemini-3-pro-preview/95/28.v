Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope string_scope.

Section CheckDictCase.

  (* Abstract types to represent Python's dynamic typing *)
  Variable Key : Type.
  Variable Value : Type.

  (* Predicates corresponding to Python's type checking and string methods *)
  Variable is_str : Key -> Prop.
  Variable is_lower : Key -> Prop.
  Variable is_upper : Key -> Prop.

  Definition check_dict_case_spec (dict : list (Key * Value)) (res : bool) : Prop :=
    let keys := map fst dict in
    match keys with
    | [] => res = false
    | _ => 
        let all_lower := Forall (fun k => is_str k /\ is_lower k) keys in
        let all_upper := Forall (fun k => is_str k /\ is_upper k) keys in
        res = true <-> (all_lower \/ all_upper)
    end.

End CheckDictCase.

(* Concrete definitions for the test case *)
Definition key_impl := string.
Definition val_impl := string.

(* Predicates for the specific test case *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := k = "first_name" \/ k = "city".
Definition is_upper_test (k : key_impl) : Prop := k = "FIRST_NAME".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("first_name", "John"); ("Age", "35"); ("city", "New York"); ("Income", "$50,000"); ("FIRST_NAME", "Jane"); ("1", "36"); ("Incyellowome", "INCOMEJohn")] false.
Proof.
  unfold check_dict_case_spec.
  simpl.
  split.
  - intros H. discriminate H.
  - intros [H_lower | H_upper].
    + inversion H_lower as [| x l Hx Hl]; subst.
      inversion Hl as [| x2 l2 Hx2 Hl2]; subst.
      destruct Hx2 as [_ H_age_lower].
      unfold is_lower_test in H_age_lower.
      destruct H_age_lower as [E1 | E2]; discriminate.
    + inversion H_upper as [| x l Hx Hl]; subst.
      destruct Hx as [_ H_fn_upper].
      unfold is_upper_test in H_fn_upper.
      discriminate H_fn_upper.
Qed.