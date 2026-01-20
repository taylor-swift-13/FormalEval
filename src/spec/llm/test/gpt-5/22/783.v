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

Parameters v1 v2 v_str3 v4 v_real1 v_minus77 v_list v_obj v_true v_false v_real2 v4b : Any.
Parameters n1 n2 n4 n_minus77 n4b : int.

Axiom IsInt_v1 : IsInt v1 n1.
Axiom IsInt_v2 : IsInt v2 n2.
Axiom NotInt_v_str3 : forall n, ~ IsInt v_str3 n.
Axiom IsInt_v4 : IsInt v4 n4.
Axiom NotInt_v_real1 : forall n, ~ IsInt v_real1 n.
Axiom IsInt_v_minus77 : IsInt v_minus77 n_minus77.
Axiom NotInt_v_list : forall n, ~ IsInt v_list n.
Axiom NotInt_v_obj : forall n, ~ IsInt v_obj n.
Axiom NotInt_v_true : forall n, ~ IsInt v_true n.
Axiom NotInt_v_false : forall n, ~ IsInt v_false n.
Axiom NotInt_v_real2 : forall n, ~ IsInt v_real2 n.
Axiom IsInt_v4b : IsInt v4b n4b.

Example test_case_mixed:
  filter_integers_spec
    [v1; v2; v_str3; v4; v_real1; v_minus77; v_list; v_obj; v_true; v_false; v_real2; v4b]
    [n1; n2; n4; n_minus77; n4b].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact IsInt_v1|].
  eapply fir_cons_int; [exact IsInt_v2|].
  eapply fir_cons_nonint; [exact NotInt_v_str3|].
  eapply fir_cons_int; [exact IsInt_v4|].
  eapply fir_cons_nonint; [exact NotInt_v_real1|].
  eapply fir_cons_int; [exact IsInt_v_minus77|].
  eapply fir_cons_nonint; [exact NotInt_v_list|].
  eapply fir_cons_nonint; [exact NotInt_v_obj|].
  eapply fir_cons_nonint; [exact NotInt_v_true|].
  eapply fir_cons_nonint; [exact NotInt_v_false|].
  eapply fir_cons_nonint; [exact NotInt_v_real2|].
  eapply fir_cons_int; [exact IsInt_v4b|].
  constructor.
Qed.