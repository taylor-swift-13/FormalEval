Require Import Coq.Lists.List.
Import ListNotations.

Parameter Any : Type.
Parameter int : Type.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Inductive filter_integers_rel : list Any -> list int -> Prop :=
| fir_nil : filter_integers_rel [] []
| fir_cons_int v n vs res :
    IsInt v n ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) (n :: res)
| fir_cons_nonint v vs res :
    (forall n, ~ IsInt v n) ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) res.

Definition filter_integers_spec (values : list Any) (res : list int) : Prop :=
  filter_integers_rel values res.

(* Parameters for the test case values *)
Parameter v_list1 : Any. (* Represents [5; 8; 1; 6] *)
Parameter v_0 : Any.     (* Represents 0 *)
Parameter v_list2 : Any. (* Represents [2; "3"] *)
Parameter v_list3 : Any. (* Represents [4] *)
Parameter v_list4 : Any. (* Represents [7; 8] *)
Parameter v_1 : Any.     (* Represents 1 *)

(* Parameters for the integer results *)
Parameter z_0 : int.     (* Represents 0 *)
Parameter z_1 : int.     (* Represents 1 *)

(* Axioms defining which values are integers *)
Axiom is_int_v0 : IsInt v_0 z_0.
Axiom is_int_v1 : IsInt v_1 z_1.
Axiom not_int_list1 : forall n, ~ IsInt v_list1 n.
Axiom not_int_list2 : forall n, ~ IsInt v_list2 n.
Axiom not_int_list3 : forall n, ~ IsInt v_list3 n.
Axiom not_int_list4 : forall n, ~ IsInt v_list4 n.

Example test_filter_integers_complex : 
  filter_integers_spec 
    [v_list1; v_0; v_list2; v_list3; v_list1; v_list1; v_list4; v_1] 
    [z_0; z_1].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_list1.
  apply fir_cons_int with (n := z_0). apply is_int_v0.
  apply fir_cons_nonint. apply not_int_list2.
  apply fir_cons_nonint. apply not_int_list3.
  apply fir_cons_nonint. apply not_int_list1.
  apply fir_cons_nonint. apply not_int_list1.
  apply fir_cons_nonint. apply not_int_list4.
  apply fir_cons_int with (n := z_1). apply is_int_v1.
  apply fir_nil.
Qed.