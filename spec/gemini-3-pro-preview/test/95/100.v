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

(* Only "ageage" is lowercase in the input keys *)
Definition is_lower_test (k : key_impl) : Prop := k = "ageage".

(* Only "LASTNAME" and "LASTENAME" are uppercase in the input keys *)
Definition is_upper_test (k : key_impl) : Prop := k = "LASTNAME" \/ k = "LASTENAME".

Definition test_input : list (key_impl * val_impl) := [
  ("firstName", "John"); 
  ("LASTNAME", "DDOE"); 
  ("Age", "D"); 
  ("cItY", "new yorAgek"); 
  ("Income", "$50,000"); 
  ("IncIome", "FIRST_NAME"); 
  ("LASTENAME", "Anew yorAgek"); 
  ("IncYorkLASTcity_NAMEPIIome", "Anenew yorAgeIncIomekw yorAgek"); 
  ("ageage", "cItYnew yorAgek")
].

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    test_input false.
Proof.
  unfold check_dict_case_spec.
  simpl.
  split.
  - intros H. discriminate.
  - intros [H_lower | H_upper].
    + (* Disprove all_lower by checking the first element "firstName" *)
      inversion H_lower as [| x l H_head H_tail].
      destruct H_head as [_ H_low].
      unfold is_lower_test in H_low.
      discriminate.
    + (* Disprove all_upper by checking the first element "firstName" *)
      inversion H_upper as [| x l H_head H_tail].
      destruct H_head as [_ H_up].
      unfold is_upper_test in H_up.
      destruct H_up; discriminate.
Qed.