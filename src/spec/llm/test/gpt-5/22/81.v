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

Parameter v_apple : Any.
Parameter v_2_71828 : Any.
Parameter v_None : Any.
Parameter v_minus2_str : Any.
Parameter v_false : Any.
Parameter v_wahellhellootermelon : Any.
Parameter v_42 : Any.
Parameter n_42 : int.
Axiom NonInt_v_apple : forall n, ~ IsInt v_apple n.
Axiom NonInt_v_2_71828 : forall n, ~ IsInt v_2_71828 n.
Axiom NonInt_v_None : forall n, ~ IsInt v_None n.
Axiom NonInt_v_minus2_str : forall n, ~ IsInt v_minus2_str n.
Axiom NonInt_v_false : forall n, ~ IsInt v_false n.
Axiom NonInt_v_wahellhellootermelon : forall n, ~ IsInt v_wahellhellootermelon n.
Axiom IsInt_v_42 : IsInt v_42 n_42.

Example test_case_mixed: filter_integers_spec [v_apple; v_2_71828; v_None; v_minus2_str; v_false; v_wahellhellootermelon; v_42] [n_42].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply NonInt_v_apple|].
  eapply fir_cons_nonint; [apply NonInt_v_2_71828|].
  eapply fir_cons_nonint; [apply NonInt_v_None|].
  eapply fir_cons_nonint; [apply NonInt_v_minus2_str|].
  eapply fir_cons_nonint; [apply NonInt_v_false|].
  eapply fir_cons_nonint; [apply NonInt_v_wahellhellootermelon|].
  eapply fir_cons_int; [apply IsInt_v_42|].
  constructor.
Qed.