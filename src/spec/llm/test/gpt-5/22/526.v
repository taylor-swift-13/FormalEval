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

Parameter v_foneour : Any.
Parameter v_5p5 : Any.
Parameter v_6 : Any.
Parameter v_seven : Any.
Parameter v_8 : Any.
Parameter v_9a : Any.
Parameter v_9b : Any.
Parameter n6 : int.
Axiom v_foneour_nonint : forall n, ~ IsInt v_foneour n.
Axiom v_5p5_nonint : forall n, ~ IsInt v_5p5 n.
Axiom v_seven_nonint : forall n, ~ IsInt v_seven n.
Axiom v_8_nonint : forall n, ~ IsInt v_8 n.
Axiom v_9a_nonint : forall n, ~ IsInt v_9a n.
Axiom v_9b_nonint : forall n, ~ IsInt v_9b n.
Axiom v_6_is_int : IsInt v_6 n6.

Example test_case_mixed: filter_integers_spec [v_foneour; v_5p5; v_6; v_seven; v_8; v_9a; v_9b] [n6].
Proof.
  unfold filter_integers_spec.
  eapply (fir_cons_nonint v_foneour); [apply v_foneour_nonint |].
  eapply (fir_cons_nonint v_5p5); [apply v_5p5_nonint |].
  eapply (fir_cons_int v_6 n6); [apply v_6_is_int |].
  eapply (fir_cons_nonint v_seven); [apply v_seven_nonint |].
  eapply (fir_cons_nonint v_8); [apply v_8_nonint |].
  eapply (fir_cons_nonint v_9a); [apply v_9a_nonint |].
  eapply (fir_cons_nonint v_9b); [apply v_9b_nonint |].
  apply fir_nil.
Qed.