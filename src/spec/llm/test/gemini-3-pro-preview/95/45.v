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
   Keys: 'first_name', 'Last_Name', 'city', 'Income', 'FIRST_NAME'
   'first_name' and 'city' are lower.
   'FIRST_NAME' is upper.
   'Last_Name' and 'Income' are mixed (neither strictly lower nor strictly upper in this context).
*)
Definition is_str_test (k : key_impl) : Prop := True.

Definition is_lower_test (k : key_impl) : Prop := 
  k = "first_name" \/ k = "city".

Definition is_upper_test (k : key_impl) : Prop := 
  k = "FIRST_NAME".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("first_name", "John"); ("Last_Name", "Doe"); ("city", "New York"); ("Income", "$50,000"); ("FIRST_NAME", "Jane")] false.
Proof.
  (* Unfold the specification definition *)
  unfold check_dict_case_spec.
  
  (* Simplify list operations (map) and let-bindings *)
  simpl.
  
  (* The goal is: false = true <-> (all_lower \/ all_upper) *)
  split.
  - (* Forward direction: false = true -> ... *)
    intros contra.
    inversion contra.
    
  - (* Backward direction: (all_lower \/ all_upper) -> false = true *)
    intros [AllLower | AllUpper].
    + (* Case: All keys are lower *)
      (* The second key "Last_Name" is not lower, which contradicts AllLower *)
      inversion AllLower; subst. (* first_name is lower, ok *)
      inversion H2; subst.       (* Last_Name is next *)
      destruct H3 as [_ HIsLower].
      unfold is_lower_test in HIsLower.
      (* HIsLower says "Last_Name" must be "first_name" or "city" *)
      destruct HIsLower as [H | H]; discriminate.
      
    + (* Case: All keys are upper *)
      (* The first key "first_name" is not upper, which contradicts AllUpper *)
      inversion AllUpper; subst. (* first_name *)
      destruct H1 as [_ HIsUpper].
      unfold is_upper_test in HIsUpper.
      (* HIsUpper says "first_name" must be "FIRST_NAME" *)
      discriminate.
Qed.