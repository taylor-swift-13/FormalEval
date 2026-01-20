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
(* None of the keys in the input are purely lowercase *)
Definition is_lower_test (k : key_impl) : Prop := False.
(* Only "LASTNAME" and "LASTNAE" are uppercase *)
Definition is_upper_test (k : key_impl) : Prop := k = "LASTNAME" \/ k = "LASTNAE".

Example test_check_dict_case_example : 
  check_dict_case_spec key_impl val_impl 
    is_str_test is_lower_test is_upper_test 
    [("firstName", "John"); ("LASTNAME", "DOE"); ("Age", "D"); ("cItY", "new yorAgek"); ("Income", "$50,000"); ("LASTNAE", "new yorAgeIncIomek")] false.
Proof.
  unfold check_dict_case_spec.
  simpl.
  split.
  - (* Forward direction: false = true -> ... *)
    intros H. inversion H.
  - (* Backward direction: (all_lower \/ all_upper) -> false = true *)
    intros [AllLower | AllUpper].
    + (* Case: All keys are lower *)
      (* The first key is "firstName". AllLower implies is_lower "firstName". *)
      inversion AllLower as [| ? ? Hhead Htail].
      destruct Hhead as [_ Hlow].
      unfold is_lower_test in Hlow.
      contradiction.
    + (* Case: All keys are upper *)
      (* The first key is "firstName". AllUpper implies is_upper "firstName". *)
      inversion AllUpper as [| ? ? Hhead Htail].
      destruct Hhead as [_ Hup].
      unfold is_upper_test in Hup.
      (* "firstName" is neither "LASTNAME" nor "LASTNAE" *)
      destruct Hup as [H_eq | H_eq]; inversion H_eq.
Qed.