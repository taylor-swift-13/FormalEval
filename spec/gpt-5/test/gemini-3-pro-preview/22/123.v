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

(* Parameters for the test case values to avoid type mismatch with literals *)
Parameter val_1 : Any. Parameter int_1 : int. Axiom is_int_1 : IsInt val_1 int_1.
Parameter val_false : Any. Axiom not_int_false : forall n, ~ IsInt val_false n.
Parameter val_2 : Any. Parameter int_2 : int. Axiom is_int_2 : IsInt val_2 int_2.
Parameter val_3 : Any. Parameter int_3 : int. Axiom is_int_3 : IsInt val_3 int_3.
Parameter val_four : Any. Axiom not_int_four : forall n, ~ IsInt val_four n.
Parameter val_5_5 : Any. Axiom not_int_5_5 : forall n, ~ IsInt val_5_5 n.
Parameter val_6 : Any. Parameter int_6 : int. Axiom is_int_6 : IsInt val_6 int_6.
Parameter val_seven : Any. Axiom not_int_seven : forall n, ~ IsInt val_seven n.
Parameter val_8_str : Any. Axiom not_int_8_str : forall n, ~ IsInt val_8_str n.
Parameter val_9_0 : Any. Axiom not_int_9_0 : forall n, ~ IsInt val_9_0 n.

(* Input: [1; false; 2; 3; "four"; 3; 5.5; 6; "seven"; "8"; 9.0; "8"] *)
(* Output: [1; 2; 3; 3; 6] *)

Example test_filter_integers_complex : 
  filter_integers_spec 
    [val_1; val_false; val_2; val_3; val_four; val_3; val_5_5; val_6; val_seven; val_8_str; val_9_0; val_8_str] 
    [int_1; int_2; int_3; int_3; int_6].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int. apply is_int_1.
  apply fir_cons_nonint. apply not_int_false.
  apply fir_cons_int. apply is_int_2.
  apply fir_cons_int. apply is_int_3.
  apply fir_cons_nonint. apply not_int_four.
  apply fir_cons_int. apply is_int_3.
  apply fir_cons_nonint. apply not_int_5_5.
  apply fir_cons_int. apply is_int_6.
  apply fir_cons_nonint. apply not_int_seven.
  apply fir_cons_nonint. apply not_int_8_str.
  apply fir_cons_nonint. apply not_int_9_0.
  apply fir_cons_nonint. apply not_int_8_str.
  apply fir_nil.
Qed.