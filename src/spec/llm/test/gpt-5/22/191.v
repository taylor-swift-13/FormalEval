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

Parameter v_m6 v_list1 v2 v0 v_list2 v_list3 v_list4 v_list5 v_list6 v1 : Any.
Parameter n_m6 n2 n0 n1 : int.
Parameter P_m6 : IsInt v_m6 n_m6.
Parameter P2 : IsInt v2 n2.
Parameter P0 : IsInt v0 n0.
Parameter P1 : IsInt v1 n1.
Parameter N_list1 : forall n, ~ IsInt v_list1 n.
Parameter N_list2 : forall n, ~ IsInt v_list2 n.
Parameter N_list3 : forall n, ~ IsInt v_list3 n.
Parameter N_list4 : forall n, ~ IsInt v_list4 n.
Parameter N_list5 : forall n, ~ IsInt v_list5 n.
Parameter N_list6 : forall n, ~ IsInt v_list6 n.

Example test_case_new:
  filter_integers_spec
    [v_m6; v_list1; v2; v0; v_list2; v_list3; v_list4; v_list5; v_list6; v1]
    [n_m6; n2; n0; n1].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact P_m6|].
  eapply fir_cons_nonint; [exact N_list1|].
  eapply fir_cons_int; [exact P2|].
  eapply fir_cons_int; [exact P0|].
  eapply fir_cons_nonint; [exact N_list2|].
  eapply fir_cons_nonint; [exact N_list3|].
  eapply fir_cons_nonint; [exact N_list4|].
  eapply fir_cons_nonint; [exact N_list5|].
  eapply fir_cons_nonint; [exact N_list6|].
  eapply fir_cons_int; [exact P1|].
  constructor.
Qed.