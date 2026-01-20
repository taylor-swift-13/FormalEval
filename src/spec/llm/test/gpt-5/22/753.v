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

Parameter v_false1 v_false2 v_none v_real v_5 v_neg7 v_0 v_str_a v_str_b v_empty_list v_empty_record v_dict_ab v_list_34 v_list_6_str7_a v_list_6_str7_b : Any.
Parameter i5 i_neg7 i0 : int.

Axiom nonint_v_false1 : forall n, ~ IsInt v_false1 n.
Axiom nonint_v_false2 : forall n, ~ IsInt v_false2 n.
Axiom nonint_v_none : forall n, ~ IsInt v_none n.
Axiom nonint_v_real : forall n, ~ IsInt v_real n.
Axiom nonint_v_str_a : forall n, ~ IsInt v_str_a n.
Axiom nonint_v_str_b : forall n, ~ IsInt v_str_b n.
Axiom nonint_v_empty_list : forall n, ~ IsInt v_empty_list n.
Axiom nonint_v_empty_record : forall n, ~ IsInt v_empty_record n.
Axiom nonint_v_dict_ab : forall n, ~ IsInt v_dict_ab n.
Axiom nonint_v_list_34 : forall n, ~ IsInt v_list_34 n.
Axiom nonint_v_list_6_str7_a : forall n, ~ IsInt v_list_6_str7_a n.
Axiom nonint_v_list_6_str7_b : forall n, ~ IsInt v_list_6_str7_b n.

Axiom isint_v_5 : IsInt v_5 i5.
Axiom isint_v_neg7 : IsInt v_neg7 i_neg7.
Axiom isint_v_0 : IsInt v_0 i0.

Example test_case_mixed:
  filter_integers_spec
    [v_false1; v_false2; v_none; v_real; v_5; v_neg7; v_0; v_str_a; v_str_b; v_empty_list; v_empty_record; v_dict_ab; v_list_34; v_list_6_str7_a; v_list_6_str7_b]
    [i5; i_neg7; i0].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply nonint_v_false1|].
  eapply fir_cons_nonint; [apply nonint_v_false2|].
  eapply fir_cons_nonint; [apply nonint_v_none|].
  eapply fir_cons_nonint; [apply nonint_v_real|].
  eapply fir_cons_int; [apply isint_v_5|].
  eapply fir_cons_int; [apply isint_v_neg7|].
  eapply fir_cons_int; [apply isint_v_0|].
  eapply fir_cons_nonint; [apply nonint_v_str_a|].
  eapply fir_cons_nonint; [apply nonint_v_str_b|].
  eapply fir_cons_nonint; [apply nonint_v_empty_list|].
  eapply fir_cons_nonint; [apply nonint_v_empty_record|].
  eapply fir_cons_nonint; [apply nonint_v_dict_ab|].
  eapply fir_cons_nonint; [apply nonint_v_list_34|].
  eapply fir_cons_nonint; [apply nonint_v_list_6_str7_a|].
  eapply fir_cons_nonint; [apply nonint_v_list_6_str7_b|].
  constructor.
Qed.