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

Parameter v_list1 v_int6 v_list2 : Any.
Parameter six : int.
Notation "6%Z" := six.
Parameter H_v_int6 : IsInt v_int6 6%Z.
Parameter H_v_list1 : forall n, ~ IsInt v_list1 n.
Parameter H_v_list2 : forall n, ~ IsInt v_list2 n.

Example test_case_new: filter_integers_spec [v_list1; v_int6; v_list2] [6%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - exact H_v_list1.
  - eapply fir_cons_int.
    + exact H_v_int6.
    + eapply fir_cons_nonint.
      * exact H_v_list2.
      * constructor.
Qed.