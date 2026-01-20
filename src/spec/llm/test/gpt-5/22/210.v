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

Parameter v6 v_list1 v1 v_empty1 v_empty2 v_list2 v7 v_empty3 : Any.
Parameter n6 n1 n7 : int.
Axiom IsInt_v6 : IsInt v6 n6.
Axiom IsInt_v1 : IsInt v1 n1.
Axiom IsInt_v7 : IsInt v7 n7.
Axiom NonInt_v_list1 : forall n, ~ IsInt v_list1 n.
Axiom NonInt_v_empty1 : forall n, ~ IsInt v_empty1 n.
Axiom NonInt_v_empty2 : forall n, ~ IsInt v_empty2 n.
Axiom NonInt_v_list2 : forall n, ~ IsInt v_list2 n.
Axiom NonInt_v_empty3 : forall n, ~ IsInt v_empty3 n.

Example test_case_mixed: filter_integers_spec [v6; v_list1; v1; v_empty1; v_empty2; v_list2; v7; v_empty3] [n6; n1; n7].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v6 |].
  eapply fir_cons_nonint; [apply NonInt_v_list1 |].
  eapply fir_cons_int; [apply IsInt_v1 |].
  eapply fir_cons_nonint; [apply NonInt_v_empty1 |].
  eapply fir_cons_nonint; [apply NonInt_v_empty2 |].
  eapply fir_cons_nonint; [apply NonInt_v_list2 |].
  eapply fir_cons_int; [apply IsInt_v7 |].
  eapply fir_cons_nonint; [apply NonInt_v_empty3 |].
  apply fir_nil.
Qed.