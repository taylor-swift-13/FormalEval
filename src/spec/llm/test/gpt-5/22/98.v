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

Parameter v_true v_none v_0 v_neg10 v_watermelon v_empty_list v_empty_record v_3_14 v_test : Any.
Parameter z0 zm10 : int.
Axiom IsInt_v_0 : IsInt v_0 z0.
Axiom IsInt_v_neg10 : IsInt v_neg10 zm10.
Axiom NotInt_v_true : forall n, ~ IsInt v_true n.
Axiom NotInt_v_none : forall n, ~ IsInt v_none n.
Axiom NotInt_v_watermelon : forall n, ~ IsInt v_watermelon n.
Axiom NotInt_v_empty_list : forall n, ~ IsInt v_empty_list n.
Axiom NotInt_v_empty_record : forall n, ~ IsInt v_empty_record n.
Axiom NotInt_v_3_14 : forall n, ~ IsInt v_3_14 n.
Axiom NotInt_v_test : forall n, ~ IsInt v_test n.

Example test_case_values: filter_integers_spec [v_true; v_none; v_0; v_neg10; v_watermelon; v_empty_list; v_empty_record; v_3_14; v_test] [z0; zm10].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [exact NotInt_v_true |].
  eapply fir_cons_nonint; [exact NotInt_v_none |].
  eapply fir_cons_int; [exact IsInt_v_0 |].
  eapply fir_cons_int; [exact IsInt_v_neg10 |].
  eapply fir_cons_nonint; [exact NotInt_v_watermelon |].
  eapply fir_cons_nonint; [exact NotInt_v_empty_list |].
  eapply fir_cons_nonint; [exact NotInt_v_empty_record |].
  eapply fir_cons_nonint; [exact NotInt_v_3_14 |].
  eapply fir_cons_nonint; [exact NotInt_v_test |].
  constructor.
Qed.