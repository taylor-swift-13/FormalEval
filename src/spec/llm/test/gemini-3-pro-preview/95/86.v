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
   keys are strings, and they are lowercase. *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := 
  k = "first_name" \/ k = "last_name" \/ k = "age" \/ k = "city" \/ k = "income".
Definition is_upper_test (k : key_impl) : Prop := False.

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("first_name", "John"); ("last_name", "Doe"); ("age", "36"); ("city", "New YorNk"); ("income", "bana")] true.
Proof.
  (* Unfold the specification definition *)
  unfold check_dict_case_spec.
  
  (* Simplify list operations (map) and let-bindings *)
  simpl.
  
  (* The goal is now: true = true <-> (all_lower \/ all_upper) *)
  split.
  - (* Forward direction: true = true -> (all_lower \/ all_upper) *)
    intros _.
    left. (* We choose the 'all_lower' branch because inputs are lowercase *)
    
    (* Prove Forall for the list *)
    constructor.
    + (* Case "first_name" *)
      split.
      * unfold is_str_test. exact I.
      * unfold is_lower_test. left. reflexivity.
    + constructor.
      * (* Case "last_name" *)
        split.
        -- unfold is_str_test. exact I.
        -- unfold is_lower_test. right. left. reflexivity.
      * constructor.
        -- (* Case "age" *)
           split.
           ++ unfold is_str_test. exact I.
           ++ unfold is_lower_test. right. right. left. reflexivity.
        -- constructor.
           ++ (* Case "city" *)
              split.
              ** unfold is_str_test. exact I.
              ** unfold is_lower_test. right. right. right. left. reflexivity.
           ++ constructor.
              ** (* Case "income" *)
                 split.
                 --- unfold is_str_test. exact I.
                 --- unfold is_lower_test. right. right. right. right. reflexivity.
              ** constructor.
        
  - (* Backward direction: (all_lower \/ all_upper) -> true = true *)
    intros _.
    reflexivity.
Qed.