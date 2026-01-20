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
   'STATE' and 'ZIP' are strings, and they are uppercase. *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := False.
Definition is_upper_test (k : key_impl) : Prop := k = "STATE" \/ k = "ZIP".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("STATE", "NC"); ("ZIP", "12345")] true.
Proof.
  (* Unfold the specification definition *)
  unfold check_dict_case_spec.
  
  (* Simplify list operations (map) and let-bindings *)
  simpl.
  
  (* The goal is now: true = true <-> (all_lower \/ all_upper) *)
  split.
  - (* Forward direction: true = true -> (all_lower \/ all_upper) *)
    intros _.
    right. (* We choose the 'all_upper' branch because inputs are uppercase *)
    
    (* Prove Forall for the list ["STATE"; "ZIP"] *)
    constructor.
    + (* Case "STATE" *)
      split.
      * (* is_str "STATE" *) unfold is_str_test. exact I.
      * (* is_upper "STATE" *) unfold is_upper_test. left. reflexivity.
    + (* Tail of list *)
      constructor.
      * (* Case "ZIP" *)
        split.
        -- (* is_str "ZIP" *) unfold is_str_test. exact I.
        -- (* is_upper "ZIP" *) unfold is_upper_test. right. reflexivity.
      * (* End of list *)
        constructor.
        
  - (* Backward direction: (all_lower \/ all_upper) -> true = true *)
    intros _.
    reflexivity.
Qed.