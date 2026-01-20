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

Parameter v61 : Any.
Parameter v_list_1_str3 : Any.
Parameter v_str4 : Any.
Parameter v_list_5_piG_6 : Any.
Parameter v7 : Any.
Parameter n61 : int.
Parameter n7 : int.

Axiom HIsInt_v61 : IsInt v61 n61.
Axiom HNonInt_v_list_1_str3 : forall n, ~ IsInt v_list_1_str3 n.
Axiom HNonInt_v_str4 : forall n, ~ IsInt v_str4 n.
Axiom HNonInt_v_list_5_piG_6 : forall n, ~ IsInt v_list_5_piG_6 n.
Axiom HIsInt_v7 : IsInt v7 n7.

Example test_case_new: filter_integers_spec [v61; v_list_1_str3; v_str4; v_list_5_piG_6; v7] [n61; n7].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply HIsInt_v61|].
  eapply fir_cons_nonint; [apply HNonInt_v_list_1_str3|].
  eapply fir_cons_nonint; [apply HNonInt_v_str4|].
  eapply fir_cons_nonint; [apply HNonInt_v_list_5_piG_6|].
  eapply fir_cons_int; [apply HIsInt_v7|].
  constructor.
Qed.