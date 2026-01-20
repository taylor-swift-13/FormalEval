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

Parameters v_list1 v7a v_str v_list2 v7b v_list3 : Any.
Parameter n7 : int.
Axiom H_v7a : IsInt v7a n7.
Axiom H_v7b : IsInt v7b n7.
Axiom H_v_list1 : forall n, ~ IsInt v_list1 n.
Axiom H_v_str : forall n, ~ IsInt v_str n.
Axiom H_v_list2 : forall n, ~ IsInt v_list2 n.
Axiom H_v_list3 : forall n, ~ IsInt v_list3 n.

Example test_case_new: filter_integers_spec [v_list1; v7a; v_str; v_list2; v7b; v_list3] [n7; n7].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint. exact H_v_list1.
  eapply fir_cons_int. exact H_v7a.
  eapply fir_cons_nonint. exact H_v_str.
  eapply fir_cons_nonint. exact H_v_list2.
  eapply fir_cons_int. exact H_v7b.
  eapply fir_cons_nonint. exact H_v_list3.
  constructor.
Qed.