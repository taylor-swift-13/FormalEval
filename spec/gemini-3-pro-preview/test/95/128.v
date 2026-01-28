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
   keys: "first_name", "Age", "FIRST_NAME", "AAge" *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := k = "first_name".
Definition is_upper_test (k : key_impl) : Prop := k = "FIRST_NAME".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("first_name", "John"); ("Age", "35"); ("FIRST_NAME", "Jane"); ("AAge", "Jcherrohn")] false.
Proof.
  (* Unfold the specification definition *)
  unfold check_dict_case_spec.
  
  (* Simplify list operations (map) and let-bindings *)
  simpl.
  
  (* The goal is now: false = true <-> (all_lower \/ all_upper) *)
  split.
  - (* Forward direction: false = true -> ... *)
    intros H. discriminate H.
        
  - (* Backward direction: (all_lower \/ all_upper) -> false = true *)
    intros [AllLower | AllUpper].
    + (* Case: All keys are lower *)
      (* "first_name" is lower, but "Age" is not *)
      inversion AllLower; subst. (* first_name *)
      inversion H2; subst. (* Age *)
      destruct H3 as [_ HAgeLower].
      unfold is_lower_test in HAgeLower.
      discriminate HAgeLower.
      
    + (* Case: All keys are upper *)
      (* "first_name" is not upper *)
      inversion AllUpper; subst. (* first_name *)
      destruct H1 as [_ HFirstUpper].
      unfold is_upper_test in HFirstUpper.
      discriminate HFirstUpper.
Qed.