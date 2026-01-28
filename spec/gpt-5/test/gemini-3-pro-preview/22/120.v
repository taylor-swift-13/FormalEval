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

Parameter i1 i4 : int.
Parameter v1 v4 : Any.
Parameter v_l23 v_l56 v_empty v_l78 v_dict v_str9 : Any.

Axiom is_int_v1 : IsInt v1 i1.
Axiom is_int_v4 : IsInt v4 i4.
Axiom not_int_l23 : forall n, ~ IsInt v_l23 n.
Axiom not_int_l56 : forall n, ~ IsInt v_l56 n.
Axiom not_int_empty : forall n, ~ IsInt v_empty n.
Axiom not_int_l78 : forall n, ~ IsInt v_l78 n.
Axiom not_int_dict : forall n, ~ IsInt v_dict n.
Axiom not_int_str9 : forall n, ~ IsInt v_str9 n.

Example test_filter_integers : 
  filter_integers_spec 
    [v1; v_l23; v4; v_l56; v_empty; v_l78; v_dict; v_str9; v_l56] 
    [i1; i4].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := i1). apply is_int_v1.
  apply fir_cons_nonint. apply not_int_l23.
  apply fir_cons_int with (n := i4). apply is_int_v4.
  apply fir_cons_nonint. apply not_int_l56.
  apply fir_cons_nonint. apply not_int_empty.
  apply fir_cons_nonint. apply not_int_l78.
  apply fir_cons_nonint. apply not_int_dict.
  apply fir_cons_nonint. apply not_int_str9.
  apply fir_cons_nonint. apply not_int_l56.
  apply fir_nil.
Qed.