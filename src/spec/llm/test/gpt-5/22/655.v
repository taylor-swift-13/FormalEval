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

Parameters v_false v_None1 v_real v_5 v_neg7 v_0 v_str_a v_str_b v_empty_obj v_dict_ab v_list_34 v_list_56_7 v_dict_floats v_None2 : Any.

Axiom NonInt_v_false : forall n, ~ IsInt v_false n.
Axiom NonInt_v_None1 : forall n, ~ IsInt v_None1 n.
Axiom NonInt_v_real : forall n, ~ IsInt v_real n.
Axiom IsInt_v_5 : IsInt v_5 (5%Z).
Axiom IsInt_v_neg7 : IsInt v_neg7 ((-7)%Z).
Axiom IsInt_v_0 : IsInt v_0 (0%Z).
Axiom NonInt_v_str_a : forall n, ~ IsInt v_str_a n.
Axiom NonInt_v_str_b : forall n, ~ IsInt v_str_b n.
Axiom NonInt_v_empty_obj : forall n, ~ IsInt v_empty_obj n.
Axiom NonInt_v_dict_ab : forall n, ~ IsInt v_dict_ab n.
Axiom NonInt_v_list_34 : forall n, ~ IsInt v_list_34 n.
Axiom NonInt_v_list_56_7 : forall n, ~ IsInt v_list_56_7 n.
Axiom NonInt_v_dict_floats : forall n, ~ IsInt v_dict_floats n.
Axiom NonInt_v_None2 : forall n, ~ IsInt v_None2 n.

Example test_case_1:
  filter_integers_spec
    [v_false; v_None1; v_real; v_5; v_neg7; v_0; v_str_a; v_str_b; v_empty_obj; v_dict_ab; v_list_34; v_list_56_7; v_dict_floats; v_None2]
    [5%Z; (-7)%Z; 0%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [exact NonInt_v_false|].
  eapply fir_cons_nonint; [exact NonInt_v_None1|].
  eapply fir_cons_nonint; [exact NonInt_v_real|].
  eapply fir_cons_int; [exact IsInt_v_5|].
  eapply fir_cons_int; [exact IsInt_v_neg7|].
  eapply fir_cons_int; [exact IsInt_v_0|].
  eapply fir_cons_nonint; [exact NonInt_v_str_a|].
  eapply fir_cons_nonint; [exact NonInt_v_str_b|].
  eapply fir_cons_nonint; [exact NonInt_v_empty_obj|].
  eapply fir_cons_nonint; [exact NonInt_v_dict_ab|].
  eapply fir_cons_nonint; [exact NonInt_v_list_34|].
  eapply fir_cons_nonint; [exact NonInt_v_list_56_7|].
  eapply fir_cons_nonint; [exact NonInt_v_dict_floats|].
  eapply fir_cons_nonint; [exact NonInt_v_None2|].
  apply fir_nil.
Qed.