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

Parameter v_minus1 v_str2 v_dict_empty v_dict_a20 v_minus57 v_list_1_2_3 v_list_4_5 : Any.
Parameter i_minus1 i_minus57 : int.

Axiom IsInt_v_minus1 : IsInt v_minus1 i_minus1.
Axiom IsInt_v_minus57 : IsInt v_minus57 i_minus57.
Axiom NonInt_v_str2 : forall n, ~ IsInt v_str2 n.
Axiom NonInt_v_dict_empty : forall n, ~ IsInt v_dict_empty n.
Axiom NonInt_v_dict_a20 : forall n, ~ IsInt v_dict_a20 n.
Axiom NonInt_v_list_1_2_3 : forall n, ~ IsInt v_list_1_2_3 n.
Axiom NonInt_v_list_4_5 : forall n, ~ IsInt v_list_4_5 n.

Example test_case_mixed:
  filter_integers_spec
    [v_minus1; v_str2; v_dict_empty; v_dict_a20; v_minus57; v_list_1_2_3; v_list_4_5; v_dict_a20]
    [i_minus1; i_minus57].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v_minus1|].
  eapply fir_cons_nonint; [apply NonInt_v_str2|].
  eapply fir_cons_nonint; [apply NonInt_v_dict_empty|].
  eapply fir_cons_nonint; [apply NonInt_v_dict_a20|].
  eapply fir_cons_int; [apply IsInt_v_minus57|].
  eapply fir_cons_nonint; [apply NonInt_v_list_1_2_3|].
  eapply fir_cons_nonint; [apply NonInt_v_list_4_5|].
  eapply fir_cons_nonint; [apply NonInt_v_dict_a20|].
  constructor.
Qed.