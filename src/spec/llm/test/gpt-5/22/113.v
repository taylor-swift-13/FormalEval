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

Parameter v_false1 v_false2 v_none v_float v5 vneg7 v0 v_str_a v_str_b v_list_empty1 v_list_empty2 v_empty_dict v_dict_ab v_list34 v_list56str : Any.
Parameter i5 ineg7 i0 : int.

Axiom IsInt_v5 : IsInt v5 i5.
Axiom IsInt_vneg7 : IsInt vneg7 ineg7.
Axiom IsInt_v0 : IsInt v0 i0.

Axiom NonInt_v_false1 : forall n, ~ IsInt v_false1 n.
Axiom NonInt_v_false2 : forall n, ~ IsInt v_false2 n.
Axiom NonInt_v_none : forall n, ~ IsInt v_none n.
Axiom NonInt_v_float : forall n, ~ IsInt v_float n.
Axiom NonInt_v_str_a : forall n, ~ IsInt v_str_a n.
Axiom NonInt_v_str_b : forall n, ~ IsInt v_str_b n.
Axiom NonInt_v_list_empty1 : forall n, ~ IsInt v_list_empty1 n.
Axiom NonInt_v_list_empty2 : forall n, ~ IsInt v_list_empty2 n.
Axiom NonInt_v_empty_dict : forall n, ~ IsInt v_empty_dict n.
Axiom NonInt_v_dict_ab : forall n, ~ IsInt v_dict_ab n.
Axiom NonInt_v_list34 : forall n, ~ IsInt v_list34 n.
Axiom NonInt_v_list56str : forall n, ~ IsInt v_list56str n.

Example test_case_new:
  filter_integers_spec
    [v_false1; v_false2; v_none; v_float; v5; vneg7; v0; v_str_a; v_str_b; v_list_empty1; v_list_empty2; v_empty_dict; v_dict_ab; v_list34; v_list56str]
    [i5; ineg7; i0].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply NonInt_v_false1 |].
  eapply fir_cons_nonint; [apply NonInt_v_false2 |].
  eapply fir_cons_nonint; [apply NonInt_v_none |].
  eapply fir_cons_nonint; [apply NonInt_v_float |].
  eapply fir_cons_int; [apply IsInt_v5 |].
  eapply fir_cons_int; [apply IsInt_vneg7 |].
  eapply fir_cons_int; [apply IsInt_v0 |].
  eapply fir_cons_nonint; [apply NonInt_v_str_a |].
  eapply fir_cons_nonint; [apply NonInt_v_str_b |].
  eapply fir_cons_nonint; [apply NonInt_v_list_empty1 |].
  eapply fir_cons_nonint; [apply NonInt_v_list_empty2 |].
  eapply fir_cons_nonint; [apply NonInt_v_empty_dict |].
  eapply fir_cons_nonint; [apply NonInt_v_dict_ab |].
  eapply fir_cons_nonint; [apply NonInt_v_list34 |].
  eapply fir_cons_nonint; [apply NonInt_v_list56str |].
  constructor.
Qed.