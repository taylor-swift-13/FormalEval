Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

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

Parameter v_true v_false v_none v_r1 v_5 v_r2 v_minus7a v_0 v_str_a v_str_b v_empty_list v_empty_obj v_dict_ab v_list_34 v_list_6_7a v_list_6_7b v_minus7b : Any.

Axiom NonInt_v_true : forall n, ~ IsInt v_true n.
Axiom NonInt_v_false : forall n, ~ IsInt v_false n.
Axiom NonInt_v_none : forall n, ~ IsInt v_none n.
Axiom NonInt_v_r1 : forall n, ~ IsInt v_r1 n.
Axiom NonInt_v_r2 : forall n, ~ IsInt v_r2 n.
Axiom NonInt_v_str_a : forall n, ~ IsInt v_str_a n.
Axiom NonInt_v_str_b : forall n, ~ IsInt v_str_b n.
Axiom NonInt_v_empty_list : forall n, ~ IsInt v_empty_list n.
Axiom NonInt_v_empty_obj : forall n, ~ IsInt v_empty_obj n.
Axiom NonInt_v_dict_ab : forall n, ~ IsInt v_dict_ab n.
Axiom NonInt_v_list_34 : forall n, ~ IsInt v_list_34 n.
Axiom NonInt_v_list_6_7a : forall n, ~ IsInt v_list_6_7a n.
Axiom NonInt_v_list_6_7b : forall n, ~ IsInt v_list_6_7b n.

Axiom IsInt_v_5 : IsInt v_5 5%Z.
Axiom IsInt_v_minus7a : IsInt v_minus7a (-7)%Z.
Axiom IsInt_v_0 : IsInt v_0 0%Z.
Axiom IsInt_v_minus7b : IsInt v_minus7b (-7)%Z.

Example test_case_new: filter_integers_spec
  [v_true; v_false; v_none; v_r1; v_5; v_r2; v_minus7a; v_0; v_str_a; v_str_b; v_empty_list; v_empty_obj; v_dict_ab; v_list_34; v_list_6_7a; v_list_6_7b; v_minus7b]
  [5%Z; (-7)%Z; 0%Z; (-7)%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [exact NonInt_v_true|].
  eapply fir_cons_nonint; [exact NonInt_v_false|].
  eapply fir_cons_nonint; [exact NonInt_v_none|].
  eapply fir_cons_nonint; [exact NonInt_v_r1|].
  eapply fir_cons_int; [exact IsInt_v_5|].
  eapply fir_cons_nonint; [exact NonInt_v_r2|].
  eapply fir_cons_int; [exact IsInt_v_minus7a|].
  eapply fir_cons_int; [exact IsInt_v_0|].
  eapply fir_cons_nonint; [exact NonInt_v_str_a|].
  eapply fir_cons_nonint; [exact NonInt_v_str_b|].
  eapply fir_cons_nonint; [exact NonInt_v_empty_list|].
  eapply fir_cons_nonint; [exact NonInt_v_empty_obj|].
  eapply fir_cons_nonint; [exact NonInt_v_dict_ab|].
  eapply fir_cons_nonint; [exact NonInt_v_list_34|].
  eapply fir_cons_nonint; [exact NonInt_v_list_6_7a|].
  eapply fir_cons_nonint; [exact NonInt_v_list_6_7b|].
  eapply fir_cons_int; [exact IsInt_v_minus7b|].
  apply fir_nil.
Qed.