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

Example test_filter_integers_complex : 
  forall (v_dict1 v_true v_false v_none v_0 v_neg10 v_str v_empty v_dict2 v_float : Any)
         (i_0 i_neg10 : int),
  (forall n, ~ IsInt v_dict1 n) ->
  (forall n, ~ IsInt v_true n) ->
  (forall n, ~ IsInt v_false n) ->
  (forall n, ~ IsInt v_none n) ->
  IsInt v_0 i_0 ->
  IsInt v_neg10 i_neg10 ->
  (forall n, ~ IsInt v_str n) ->
  (forall n, ~ IsInt v_empty n) ->
  (forall n, ~ IsInt v_dict2 n) ->
  (forall n, ~ IsInt v_float n) ->
  filter_integers_spec 
    [v_dict1; v_true; v_false; v_none; v_0; v_neg10; v_str; v_empty; v_dict2; v_float] 
    [i_0; i_neg10].
Proof.
  intros v_dict1 v_true v_false v_none v_0 v_neg10 v_str v_empty v_dict2 v_float i_0 i_neg10.
  intros H_dict1 H_true H_false H_none H_is_0 H_is_neg10 H_str H_empty H_dict2 H_float.
  unfold filter_integers_spec.
  apply fir_cons_nonint. exact H_dict1.
  apply fir_cons_nonint. exact H_true.
  apply fir_cons_nonint. exact H_false.
  apply fir_cons_nonint. exact H_none.
  apply fir_cons_int with (n := i_0). exact H_is_0.
  apply fir_cons_int with (n := i_neg10). exact H_is_neg10.
  apply fir_cons_nonint. exact H_str.
  apply fir_cons_nonint. exact H_empty.
  apply fir_cons_nonint. exact H_dict2.
  apply fir_cons_nonint. exact H_float.
  apply fir_nil.
Qed.