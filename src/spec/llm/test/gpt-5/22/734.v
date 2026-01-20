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

Example test_case_nonempty :
  forall (v_true v_false v_none v_float v5 v_neg7 v0 v_str v_empty1 v_empty2 v_obj v_dict v_list1 v_list2 : Any)
         (n5 nneg7 n0 : int),
    (forall n, ~ IsInt v_true n) ->
    (forall n, ~ IsInt v_false n) ->
    (forall n, ~ IsInt v_none n) ->
    (forall n, ~ IsInt v_float n) ->
    IsInt v5 n5 ->
    IsInt v_neg7 nneg7 ->
    IsInt v0 n0 ->
    (forall n, ~ IsInt v_str n) ->
    (forall n, ~ IsInt v_empty1 n) ->
    (forall n, ~ IsInt v_empty2 n) ->
    (forall n, ~ IsInt v_obj n) ->
    (forall n, ~ IsInt v_dict n) ->
    (forall n, ~ IsInt v_list1 n) ->
    (forall n, ~ IsInt v_list2 n) ->
    filter_integers_spec
      [v_true; v_false; v_none; v_float; v5; v_neg7; v0; v_str; v_empty1; v_empty2; v_obj; v_dict; v_list1; v_list2]
      [n5; nneg7; n0].
Proof.
  intros v_true v_false v_none v_float v5 v_neg7 v0 v_str v_empty1 v_empty2 v_obj v_dict v_list1 v_list2
         n5 nneg7 n0
         H_true H_false H_none H_float H5 Hneg7 H0 H_str H_empty1 H_empty2 H_obj H_dict H_list1 H_list2.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [exact H_true|].
  eapply fir_cons_nonint; [exact H_false|].
  eapply fir_cons_nonint; [exact H_none|].
  eapply fir_cons_nonint; [exact H_float|].
  eapply fir_cons_int; [exact H5|].
  eapply fir_cons_int; [exact Hneg7|].
  eapply fir_cons_int; [exact H0|].
  eapply fir_cons_nonint; [exact H_str|].
  eapply fir_cons_nonint; [exact H_empty1|].
  eapply fir_cons_nonint; [exact H_empty2|].
  eapply fir_cons_nonint; [exact H_obj|].
  eapply fir_cons_nonint; [exact H_dict|].
  eapply fir_cons_nonint; [exact H_list1|].
  eapply fir_cons_nonint; [exact H_list2|].
  constructor.
Qed.