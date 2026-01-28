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

Parameter v1 v2 v4 : Any.
Parameter v_str v_float v_list v_map : Any.
Parameter i1 i2 i4 : int.

Axiom is_int_v1 : IsInt v1 i1.
Axiom is_int_v2 : IsInt v2 i2.
Axiom is_int_v4 : IsInt v4 i4.

Axiom not_int_str : forall n, ~ IsInt v_str n.
Axiom not_int_float : forall n, ~ IsInt v_float n.
Axiom not_int_list : forall n, ~ IsInt v_list n.
Axiom not_int_map : forall n, ~ IsInt v_map n.

Example test_filter_integers_mixed :
  filter_integers_spec
    [v1; v2; v_str; v4; v_float; v_list; v_map; v1]
    [i1; i2; i4; i1].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int. apply is_int_v1.
  apply fir_cons_int. apply is_int_v2.
  apply fir_cons_nonint. apply not_int_str.
  apply fir_cons_int. apply is_int_v4.
  apply fir_cons_nonint. apply not_int_float.
  apply fir_cons_nonint. apply not_int_list.
  apply fir_cons_nonint. apply not_int_map.
  apply fir_cons_int. apply is_int_v1.
  apply fir_nil.
Qed.