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
(* We use string to represent the float value 3.14159 to keep imports minimal, 
   as the value content does not affect the logic of this specification. *)
Definition val_impl := string.

(* Predicates for the specific test case: 
   'PI' is a string, and it is uppercase. *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := False.
Definition is_upper_test (k : key_impl) : Prop := k = "PI".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("PI", "3.14159")] true.
Proof.
  (* Unfold the specification definition *)
  unfold check_dict_case_spec.
  
  (* Simplify list operations (map) and let-bindings *)
  simpl.
  
  (* The goal is now: true = true <-> (all_lower \/ all_upper) *)
  split.
  - (* Forward direction: true = true -> (all_lower \/ all_upper) *)
    intros _.
    right. (* We choose the 'all_upper' branch because the key is uppercase *)
    
    (* Prove Forall for the list ["PI"] *)
    constructor.
    + (* Case "PI" *)
      split.
      * (* is_str "PI" *) unfold is_str_test. exact I.
      * (* is_upper "PI" *) unfold is_upper_test. reflexivity.
    + (* Tail of list *)
      constructor.
        
  - (* Backward direction: (all_lower \/ all_upper) -> true = true *)
    intros _.
    reflexivity.
Qed.