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

Parameter v_r1 v_r2 v_r3 v_str v_obj v_list : Any.
Axiom v_r1_nonint : forall n, ~ IsInt v_r1 n.
Axiom v_r2_nonint : forall n, ~ IsInt v_r2 n.
Axiom v_r3_nonint : forall n, ~ IsInt v_r3 n.
Axiom v_str_nonint : forall n, ~ IsInt v_str n.
Axiom v_obj_nonint : forall n, ~ IsInt v_obj n.
Axiom v_list_nonint : forall n, ~ IsInt v_list n.

Example test_case_nonints: filter_integers_spec [v_r1; v_r2; v_r3; v_str; v_obj; v_list] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply v_r1_nonint |].
  eapply fir_cons_nonint; [apply v_r2_nonint |].
  eapply fir_cons_nonint; [apply v_r3_nonint |].
  eapply fir_cons_nonint; [apply v_str_nonint |].
  eapply fir_cons_nonint; [apply v_obj_nonint |].
  eapply fir_cons_nonint; [apply v_list_nonint |].
  constructor.
Qed.