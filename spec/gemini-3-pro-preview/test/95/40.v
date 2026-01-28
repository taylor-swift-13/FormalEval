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
   is_lower is true only for 'first_name' and 'city'
   is_upper is true only for 'FIRST_NAME' *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := k = "first_name" \/ k = "city".
Definition is_upper_test (k : key_impl) : Prop := k = "FIRST_NAME".

(* Input list corresponding to: 
   [{'first_name': 'John', 'Last_Name': 'Doe', 'Age': 35, 'city': 'new yorAgek', 'Income': '$50,000', 'FIRST_NAME': 'Jane'}] 
   Note: Values are simplified to strings as their content doesn't affect the logic. *)
Definition input_data : list (key_impl * val_impl) := [
  ("first_name", "John");
  ("Last_Name", "Doe");
  ("Age", "35");
  ("city", "new yorAgek");
  ("Income", "$50,000");
  ("FIRST_NAME", "Jane")
].

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    input_data false.
Proof.
  (* Unfold the specification definition *)
  unfold check_dict_case_spec.
  
  (* Simplify list operations (map) and let-bindings *)
  simpl.
  
  (* The goal is: false = true <-> (all_lower \/ all_upper) *)
  split.
  - (* Forward direction: false = true -> ... *)
    intros H. inversion H.
    
  - (* Backward direction: (all_lower \/ all_upper) -> false = true *)
    intros [H_lower | H_upper].
    + (* Case: all_lower is assumed true. We derive a contradiction. *)
      (* The list is ["first_name"; "Last_Name"; ...]. "Last_Name" is not lower. *)
      (* Decompose Forall for the first element *)
      inversion H_lower as [| k1 l1 H1 H_tail1]. subst.
      (* Decompose Forall for the second element *)
      inversion H_tail1 as [| k2 l2 H2 H_tail2]. subst.
      (* k2 is "Last_Name". H2 implies is_lower "Last_Name" *)
      destruct H2 as [_ H_k2_lower].
      unfold is_lower_test in H_k2_lower.
      (* "Last_Name" = "first_name" \/ "Last_Name" = "city" *)
      destruct H_k2_lower as [E1 | E2]; inversion E1 || inversion E2.
      
    + (* Case: all_upper is assumed true. We derive a contradiction. *)
      (* The list starts with "first_name". It is not upper. *)
      inversion H_upper as [| k1 l1 H1 H_tail1]. subst.
      (* k1 is "first_name". H1 implies is_upper "first_name" *)
      destruct H1 as [_ H_k1_upper].
      unfold is_upper_test in H_k1_upper.
      (* "first_name" = "FIRST_NAME" *)
      inversion H_k1_upper.
Qed.