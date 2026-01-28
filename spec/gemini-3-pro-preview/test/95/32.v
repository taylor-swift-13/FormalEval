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
(* None of the keys are all lowercase *)
Definition is_lower_test (k : key_impl) : Prop := False.
(* Only 'LASTNAME' is all uppercase *)
Definition is_upper_test (k : key_impl) : Prop := k = "LASTNAME".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("firstName", "John"); ("LASTNAME", "DOE"); ("Age", "D"); ("cItY", "new yorAgek"); ("Income", "$50,000")] false.
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
    intros [H_lower | H_upper].
    + (* Case: all_lower is true *)
      (* The first key is "firstName", check if it satisfies is_lower *)
      inversion H_lower. subst.
      destruct H1 as [_ H_lower_firstName].
      unfold is_lower_test in H_lower_firstName.
      contradiction.
    + (* Case: all_upper is true *)
      (* The first key is "firstName", check if it satisfies is_upper *)
      inversion H_upper. subst.
      destruct H1 as [_ H_upper_firstName].
      unfold is_upper_test in H_upper_firstName.
      (* "firstName" = "LASTNAME" is false *)
      inversion H_upper_firstName.
Qed.