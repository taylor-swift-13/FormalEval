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

Parameters v_false v_None v_1p3 v_5 v_m7 v_0 v_a v_b v_empty_dict v_dict_ab v_list_5_6_7 : Any.
Parameters i5 im7 i0 : int.

Axiom isint_v_5 : IsInt v_5 i5.
Axiom isint_v_m7 : IsInt v_m7 im7.
Axiom isint_v_0 : IsInt v_0 i0.

Axiom nonint_v_false : forall n, ~ IsInt v_false n.
Axiom nonint_v_None : forall n, ~ IsInt v_None n.
Axiom nonint_v_1p3 : forall n, ~ IsInt v_1p3 n.
Axiom nonint_v_a : forall n, ~ IsInt v_a n.
Axiom nonint_v_b : forall n, ~ IsInt v_b n.
Axiom nonint_v_empty_dict : forall n, ~ IsInt v_empty_dict n.
Axiom nonint_v_dict_ab : forall n, ~ IsInt v_dict_ab n.
Axiom nonint_v_list_5_6_7 : forall n, ~ IsInt v_list_5_6_7 n.

Example test_case_new:
  filter_integers_spec
    [v_false; v_None; v_1p3; v_5; v_m7; v_0; v_a; v_b; v_empty_dict; v_dict_ab; v_list_5_6_7]
    [i5; im7; i0].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [exact nonint_v_false|].
  eapply fir_cons_nonint; [exact nonint_v_None|].
  eapply fir_cons_nonint; [exact nonint_v_1p3|].
  eapply fir_cons_int; [exact isint_v_5|].
  eapply fir_cons_int; [exact isint_v_m7|].
  eapply fir_cons_int; [exact isint_v_0|].
  eapply fir_cons_nonint; [exact nonint_v_a|].
  eapply fir_cons_nonint; [exact nonint_v_b|].
  eapply fir_cons_nonint; [exact nonint_v_empty_dict|].
  eapply fir_cons_nonint; [exact nonint_v_dict_ab|].
  eapply fir_cons_nonint; [exact nonint_v_list_5_6_7|].
  constructor.
Qed.