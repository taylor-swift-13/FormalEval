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
Definition is_lower_test (k : key_impl) : Prop := 
  k = "first_name" \/ k = "city".
Definition is_upper_test (k : key_impl) : Prop := 
  k = "FIRST_NAME".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("first_name", "John"); ("Last_Name", "Dooe"); ("Age", "35"); 
     ("city", "New York"); ("Income", "$50,000"); ("FIRST_NAME", "Anew"); 
     ("1", "36"); ("Incyellowome", "INCOMEJohn"); ("chINCEOMEerryAge", "$50,00")] false.
Proof.
  unfold check_dict_case_spec.
  simpl.
  split.
  - intros H.
    discriminate.
  - intros [Hlower | Hupper].
    + inversion Hlower as [| k1 l1 H1 Htail1]. subst.
      inversion Htail1 as [| k2 l2 H2 Htail2]. subst.
      destruct H2 as [_ Hlow].
      compute in Hlow.
      destruct Hlow; discriminate.
    + inversion Hupper as [| k1 l1 H1 Htail1]. subst.
      destruct H1 as [_ Hup].
      compute in Hup.
      discriminate.
Qed.