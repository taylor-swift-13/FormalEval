Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.

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

(* Concrete instantiation for the test case *)
Section TestCase.

  (* Define concrete key and value types *)
  Inductive TestKey : Type :=
  | key_p : TestKey
  | key_b : TestKey.

  Inductive TestValue : Type :=
  | val_pineapple : TestValue
  | val_banana : TestValue.

  (* Define predicates for our concrete types *)
  Definition test_is_str (k : TestKey) : Prop := True.
  
  Definition test_is_lower (k : TestKey) : Prop :=
    match k with
    | key_p => True
    | key_b => True
    end.

  Definition test_is_upper (k : TestKey) : Prop :=
    match k with
    | key_p => False
    | key_b => False
    end.

  (* The test dictionary *)
  Definition test_dict : list (TestKey * TestValue) :=
    [(key_p, val_pineapple); (key_b, val_banana)].

  (* The expected output *)
  Definition test_output : bool := true.

  Example test_check_dict_case :
    check_dict_case_spec TestKey TestValue test_is_str test_is_lower test_is_upper test_dict test_output.
  Proof.
    unfold check_dict_case_spec.
    unfold test_dict.
    simpl.
    split.
    - intros _.
      left.
      repeat constructor; unfold test_is_str, test_is_lower; auto.
    - intros _.
      reflexivity.
  Qed.

End TestCase.