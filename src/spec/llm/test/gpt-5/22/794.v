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

Parameter v_str3 : Any.
Parameter v1 : Any.
Parameter v_cusZwMFvpu : Any.
Parameter v_list_5_6_5 : Any.
Parameter v7 : Any.

Hypothesis NonInt_v_str3 : forall n, ~ IsInt v_str3 n.
Hypothesis IsInt_v1 : IsInt v1 1%Z.
Hypothesis NonInt_v_cusZwMFvpu : forall n, ~ IsInt v_cusZwMFvpu n.
Hypothesis NonInt_v_list_5_6_5 : forall n, ~ IsInt v_list_5_6_5 n.
Hypothesis IsInt_v7 : IsInt v7 7%Z.

Example test_case_filtered: filter_integers_spec [v_str3; v1; v_cusZwMFvpu; v_list_5_6_5; v_list_5_6_5; v7; v_list_5_6_5] [1%Z; 7%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint. intro n; apply NonInt_v_str3.
  eapply fir_cons_int. apply IsInt_v1.
  eapply fir_cons_nonint. intro n; apply NonInt_v_cusZwMFvpu.
  eapply fir_cons_nonint. intro n; apply NonInt_v_list_5_6_5.
  eapply fir_cons_nonint. intro n; apply NonInt_v_list_5_6_5.
  eapply fir_cons_int. apply IsInt_v7.
  eapply fir_cons_nonint. intro n; apply NonInt_v_list_5_6_5.
  apply fir_nil.
Qed.