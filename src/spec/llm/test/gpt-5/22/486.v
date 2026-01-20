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
  v_false1 v_false2 v_none v_real v_int5 v_list5_7a v_neg7 v_zero v_a v_b
  v_empty1 v_empty2 v_dict1 v_emptydict v_dict2 v_list3_4 v_list5_7b : Any.

Parameters i5 i_neg7 i0 : int.

Axiom H_int5 : IsInt v_int5 i5.
Axiom H_neg7 : IsInt v_neg7 i_neg7.
Axiom H_0 : IsInt v_zero i0.

Axiom H_nonint_false1 : forall n, ~ IsInt v_false1 n.
Axiom H_nonint_false2 : forall n, ~ IsInt v_false2 n.
Axiom H_nonint_none : forall n, ~ IsInt v_none n.
Axiom H_nonint_real : forall n, ~ IsInt v_real n.
Axiom H_nonint_list5_7a : forall n, ~ IsInt v_list5_7a n.
Axiom H_nonint_a : forall n, ~ IsInt v_a n.
Axiom H_nonint_b : forall n, ~ IsInt v_b n.
Axiom H_nonint_empty1 : forall n, ~ IsInt v_empty1 n.
Axiom H_nonint_empty2 : forall n, ~ IsInt v_empty2 n.
Axiom H_nonint_dict1 : forall n, ~ IsInt v_dict1 n.
Axiom H_nonint_emptydict : forall n, ~ IsInt v_emptydict n.
Axiom H_nonint_dict2 : forall n, ~ IsInt v_dict2 n.
Axiom H_nonint_list3_4 : forall n, ~ IsInt v_list3_4 n.
Axiom H_nonint_list5_7b : forall n, ~ IsInt v_list5_7b n.

Example test_case_complex: filter_integers_spec
  [v_false1; v_false2; v_none; v_real; v_int5; v_list5_7a; v_neg7; v_zero; v_a; v_b; v_empty1; v_empty2; v_dict1; v_emptydict; v_dict2; v_list3_4; v_list5_7b]
  [i5; i_neg7; i0].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply H_nonint_false1|].
  eapply fir_cons_nonint; [apply H_nonint_false2|].
  eapply fir_cons_nonint; [apply H_nonint_none|].
  eapply fir_cons_nonint; [apply H_nonint_real|].
  eapply fir_cons_int; [apply H_int5|].
  eapply fir_cons_nonint; [apply H_nonint_list5_7a|].
  eapply fir_cons_int; [apply H_neg7|].
  eapply fir_cons_int; [apply H_0|].
  eapply fir_cons_nonint; [apply H_nonint_a|].
  eapply fir_cons_nonint; [apply H_nonint_b|].
  eapply fir_cons_nonint; [apply H_nonint_empty1|].
  eapply fir_cons_nonint; [apply H_nonint_empty2|].
  eapply fir_cons_nonint; [apply H_nonint_dict1|].
  eapply fir_cons_nonint; [apply H_nonint_emptydict|].
  eapply fir_cons_nonint; [apply H_nonint_dict2|].
  eapply fir_cons_nonint; [apply H_nonint_list3_4|].
  eapply fir_cons_nonint; [apply H_nonint_list5_7b|].
  constructor.
Qed.