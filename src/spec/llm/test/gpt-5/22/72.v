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

Parameter v_hello : Any.
Parameter v_how1 : Any.
Parameter v_world : Any.
Parameter v_how2 : Any.
Parameter v_empty : Any.
Parameter v_ho2w : Any.
Parameter v_worldhowhow : Any.
Parameter v_test : Any.
Parameter v_you : Any.

Axiom hello_not_int : forall n, ~ IsInt v_hello n.
Axiom how1_not_int : forall n, ~ IsInt v_how1 n.
Axiom world_not_int : forall n, ~ IsInt v_world n.
Axiom how2_not_int : forall n, ~ IsInt v_how2 n.
Axiom empty_not_int : forall n, ~ IsInt v_empty n.
Axiom ho2w_not_int : forall n, ~ IsInt v_ho2w n.
Axiom worldhowhow_not_int : forall n, ~ IsInt v_worldhowhow n.
Axiom test_not_int : forall n, ~ IsInt v_test n.
Axiom you_not_int : forall n, ~ IsInt v_you n.

Example test_case_strings: filter_integers_spec [v_hello; v_how1; v_world; v_how2; v_empty; v_ho2w; v_worldhowhow; v_test; v_you] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [exact hello_not_int|].
  eapply fir_cons_nonint; [exact how1_not_int|].
  eapply fir_cons_nonint; [exact world_not_int|].
  eapply fir_cons_nonint; [exact how2_not_int|].
  eapply fir_cons_nonint; [exact empty_not_int|].
  eapply fir_cons_nonint; [exact ho2w_not_int|].
  eapply fir_cons_nonint; [exact worldhowhow_not_int|].
  eapply fir_cons_nonint; [exact test_not_int|].
  eapply fir_cons_nonint; [exact you_not_int|].
  constructor.
Qed.