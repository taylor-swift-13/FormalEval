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
Inductive val_impl := 
  | VStr (s : string)
  | VInt (n : nat).

(* Predicates for the specific test case: 
   All keys are strings and are uppercase. *)
Definition is_str_test (k : key_impl) : Prop := True.
Definition is_lower_test (k : key_impl) : Prop := False.
Definition is_upper_test (k : key_impl) : Prop := True.

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("FIRST_NAME", VStr "John"); 
     ("LAST_NAME", VStr "DOE"); 
     ("AGE", VInt 35); 
     ("CITY", VStr "NEW YORK"); 
     ("INCOME", VStr "$50,000"); 
     ("COME", VStr "$50,0000")] true.
Proof.
  unfold check_dict_case_spec.
  simpl.
  split.
  - intros _.
    right.
    repeat constructor.
  - intros _.
    reflexivity.
Qed.