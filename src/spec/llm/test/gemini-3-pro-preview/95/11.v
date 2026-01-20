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

(* Predicates for the specific test case: 
   'first_name' and 'city' are lowercase. 'FIRST_NAME' is uppercase. Others are mixed. *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := k = "first_name" \/ k = "city".
Definition is_upper_test (k : key_impl) : Prop := k = "FIRST_NAME".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("first_name", "John"); ("Last_Name", "Doe"); ("Age", "35"); ("city", "New York"); ("Income", "$50,000"); ("FIRST_NAME", "Jane")] false.
Proof.
  (* Unfold the specification definition *)
  unfold check_dict_case_spec.
  
  (* Simplify list operations (map) and let-bindings *)
  simpl.
  
  (* The goal is now: false = true <-> (all_lower \/ all_upper) *)
  split.
  - (* Forward direction: false = true -> ... *)
    intros H. inversion H.
        
  - (* Backward direction: (all_lower \/ all_upper) -> false = true *)
    intros [H_all_lower | H_all_upper].
    + (* Case: all_lower is true *)
      (* The list is ["first_name"; "Last_Name"; "Age"; "city"; "Income"; "FIRST_NAME"] *)
      (* "first_name" satisfies is_lower, so we skip it *)
      inversion H_all_lower; subst.
      (* "Last_Name" is next. It does NOT satisfy is_lower *)
      inversion H2; subst.
      destruct H3 as [_ H_contra].
      unfold is_lower_test in H_contra.
      destruct H_contra as [H_eq | H_eq]; discriminate.
      
    + (* Case: all_upper is true *)
      (* "first_name" is the first element. It does NOT satisfy is_upper *)
      inversion H_all_upper; subst.
      destruct H1 as [_ H_contra].
      unfold is_upper_test in H_contra.
      discriminate.
Qed.