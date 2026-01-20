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

Parameter a_apple a_appaapplebcle a_2_71828_R1 a_None a_false a_watermelon a_42 a_2_71828_R2 a_apple2 : Any.
Axiom nonint_apple : forall n, ~ IsInt a_apple n.
Axiom nonint_appaapplebcle : forall n, ~ IsInt a_appaapplebcle n.
Axiom nonint_2_71828_R1 : forall n, ~ IsInt a_2_71828_R1 n.
Axiom nonint_None : forall n, ~ IsInt a_None n.
Axiom nonint_false : forall n, ~ IsInt a_false n.
Axiom nonint_watermelon : forall n, ~ IsInt a_watermelon n.
Axiom is_int_42 : IsInt a_42 42%Z.
Axiom nonint_2_71828_R2 : forall n, ~ IsInt a_2_71828_R2 n.
Axiom nonint_apple2 : forall n, ~ IsInt a_apple2 n.

Example test_case_mixed:
  filter_integers_spec
    [a_apple; a_appaapplebcle; a_2_71828_R1; a_None; a_false; a_watermelon; a_42; a_2_71828_R2; a_apple2]
    [42%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply nonint_apple|].
  eapply fir_cons_nonint; [apply nonint_appaapplebcle|].
  eapply fir_cons_nonint; [apply nonint_2_71828_R1|].
  eapply fir_cons_nonint; [apply nonint_None|].
  eapply fir_cons_nonint; [apply nonint_false|].
  eapply fir_cons_nonint; [apply nonint_watermelon|].
  eapply fir_cons_int; [apply is_int_42|].
  eapply fir_cons_nonint; [apply nonint_2_71828_R2|].
  eapply fir_cons_nonint; [apply nonint_apple2|].
  apply fir_nil.
Qed.