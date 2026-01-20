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

Parameter v_int1 v_str2_1 v_dict_1 v_list_123 v_list_45 v_dict_six v_dict_2 v_str2_2 : Any.
Parameter one_int : int.
Notation "1%Z" := one_int.
Axiom H_int1 : IsInt v_int1 1%Z.
Axiom H_nonint_str2_1 : forall n, ~ IsInt v_str2_1 n.
Axiom H_nonint_dict_1 : forall n, ~ IsInt v_dict_1 n.
Axiom H_nonint_list_123 : forall n, ~ IsInt v_list_123 n.
Axiom H_nonint_list_45 : forall n, ~ IsInt v_list_45 n.
Axiom H_nonint_dict_six : forall n, ~ IsInt v_dict_six n.
Axiom H_nonint_dict_2 : forall n, ~ IsInt v_dict_2 n.
Axiom H_nonint_str2_2 : forall n, ~ IsInt v_str2_2 n.

Example test_case_mixed: filter_integers_spec [v_int1; v_str2_1; v_dict_1; v_list_123; v_list_45; v_dict_six; v_dict_2; v_str2_2] [1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply H_int1 |].
  eapply fir_cons_nonint; [apply H_nonint_str2_1 |].
  eapply fir_cons_nonint; [apply H_nonint_dict_1 |].
  eapply fir_cons_nonint; [apply H_nonint_list_123 |].
  eapply fir_cons_nonint; [apply H_nonint_list_45 |].
  eapply fir_cons_nonint; [apply H_nonint_dict_six |].
  eapply fir_cons_nonint; [apply H_nonint_dict_2 |].
  eapply fir_cons_nonint; [apply H_nonint_str2_2 |].
  constructor.
Qed.