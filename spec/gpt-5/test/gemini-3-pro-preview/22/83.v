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

Parameter v_float1 : Any. (* 7.8 *)
Axiom not_int_float1 : forall n, ~ IsInt v_float1 n.

Parameter v_str : Any. (* "aapplebc" *)
Axiom not_int_str : forall n, ~ IsInt v_str n.

Parameter v_dict : Any. (* {} *)
Axiom not_int_dict : forall n, ~ IsInt v_dict n.

Parameter v_list : Any. (* [] *)
Axiom not_int_list : forall n, ~ IsInt v_list n.

Parameter v_float2 : Any. (* 2.5 *)
Axiom not_int_float2 : forall n, ~ IsInt v_float2 n.

Example test_filter_integers_mixed : 
  filter_integers_spec [v_float1; v_str; v_dict; v_list; v_float2; v_list] [].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply not_int_float1.
  apply fir_cons_nonint. apply not_int_str.
  apply fir_cons_nonint. apply not_int_dict.
  apply fir_cons_nonint. apply not_int_list.
  apply fir_cons_nonint. apply not_int_float2.
  apply fir_cons_nonint. apply not_int_list.
  apply fir_nil.
Qed.