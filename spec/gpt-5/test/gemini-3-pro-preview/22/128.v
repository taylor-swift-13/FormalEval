Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
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

Parameter v_1 : Any.
Axiom is_int_v_1 : IsInt v_1 1%Z.

Parameter v_nil : Any.
Axiom not_int_v_nil : forall n, ~ IsInt v_nil n.

Parameter v_8 : Any.
Axiom is_int_v_8 : IsInt v_8 8%Z.

Parameter v_list_5 : Any.
Axiom not_int_v_list_5 : forall n, ~ IsInt v_list_5 n.

Parameter v_list_7_8 : Any.
Axiom not_int_v_list_7_8 : forall n, ~ IsInt v_list_7_8 n.

Parameter v_9 : Any.
Axiom is_int_v_9 : IsInt v_9 9%Z.

Parameter v_mix : Any.
Axiom not_int_v_mix : forall n, ~ IsInt v_mix n.

Example test_filter_integers : 
  filter_integers_spec 
    [v_1; v_nil; v_nil; v_8; v_list_5; v_list_7_8; v_9; v_9; v_mix; v_list_7_8] 
    [1%Z; 8%Z; 9%Z; 9%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 1%Z). apply is_int_v_1.
  apply fir_cons_nonint. apply not_int_v_nil.
  apply fir_cons_nonint. apply not_int_v_nil.
  apply fir_cons_int with (n := 8%Z). apply is_int_v_8.
  apply fir_cons_nonint. apply not_int_v_list_5.
  apply fir_cons_nonint. apply not_int_v_list_7_8.
  apply fir_cons_int with (n := 9%Z). apply is_int_v_9.
  apply fir_cons_int with (n := 9%Z). apply is_int_v_9.
  apply fir_cons_nonint. apply not_int_v_mix.
  apply fir_cons_nonint. apply not_int_v_list_7_8.
  apply fir_nil.
Qed.