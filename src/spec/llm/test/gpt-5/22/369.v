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

Parameters
  v_true v_false v_none v_real v_5 v_minus7 v_0 v_a v_b v_nil1 v_nil2
  v_list4_1 v_emptyset v_dict_ab v_list4_2 v_list_mixed v_list4_3 : Any.

Parameters z5 zminus7 z0 : int.

Axiom IsInt_v_5 : IsInt v_5 z5.
Axiom IsInt_v_minus7 : IsInt v_minus7 zminus7.
Axiom IsInt_v_0 : IsInt v_0 z0.

Axiom NonInt_v_true : forall n, ~ IsInt v_true n.
Axiom NonInt_v_false : forall n, ~ IsInt v_false n.
Axiom NonInt_v_none : forall n, ~ IsInt v_none n.
Axiom NonInt_v_real : forall n, ~ IsInt v_real n.
Axiom NonInt_v_a : forall n, ~ IsInt v_a n.
Axiom NonInt_v_b : forall n, ~ IsInt v_b n.
Axiom NonInt_v_nil1 : forall n, ~ IsInt v_nil1 n.
Axiom NonInt_v_nil2 : forall n, ~ IsInt v_nil2 n.
Axiom NonInt_v_list4_1 : forall n, ~ IsInt v_list4_1 n.
Axiom NonInt_v_emptyset : forall n, ~ IsInt v_emptyset n.
Axiom NonInt_v_dict_ab : forall n, ~ IsInt v_dict_ab n.
Axiom NonInt_v_list4_2 : forall n, ~ IsInt v_list4_2 n.
Axiom NonInt_v_list_mixed : forall n, ~ IsInt v_list_mixed n.
Axiom NonInt_v_list4_3 : forall n, ~ IsInt v_list4_3 n.

Example test_case_mixed:
  filter_integers_spec
    [v_true; v_false; v_none; v_real; v_5; v_minus7; v_0; v_a; v_b; v_nil1; v_nil2;
     v_list4_1; v_emptyset; v_dict_ab; v_list4_2; v_list_mixed; v_list4_3]
    [z5; zminus7; z0].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply NonInt_v_true|].
  eapply fir_cons_nonint; [apply NonInt_v_false|].
  eapply fir_cons_nonint; [apply NonInt_v_none|].
  eapply fir_cons_nonint; [apply NonInt_v_real|].
  eapply fir_cons_int; [apply IsInt_v_5|].
  eapply fir_cons_int; [apply IsInt_v_minus7|].
  eapply fir_cons_int; [apply IsInt_v_0|].
  eapply fir_cons_nonint; [apply NonInt_v_a|].
  eapply fir_cons_nonint; [apply NonInt_v_b|].
  eapply fir_cons_nonint; [apply NonInt_v_nil1|].
  eapply fir_cons_nonint; [apply NonInt_v_nil2|].
  eapply fir_cons_nonint; [apply NonInt_v_list4_1|].
  eapply fir_cons_nonint; [apply NonInt_v_emptyset|].
  eapply fir_cons_nonint; [apply NonInt_v_dict_ab|].
  eapply fir_cons_nonint; [apply NonInt_v_list4_2|].
  eapply fir_cons_nonint; [apply NonInt_v_list_mixed|].
  eapply fir_cons_nonint; [apply NonInt_v_list4_3|].
  constructor.
Qed.