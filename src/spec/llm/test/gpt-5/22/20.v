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

Parameter apple real nonev falsev watermelon v42 : Any.
Parameter n42 : int.
Axiom apple_nonint : forall n, ~ IsInt apple n.
Axiom real_nonint : forall n, ~ IsInt real n.
Axiom nonev_nonint : forall n, ~ IsInt nonev n.
Axiom falsev_nonint : forall n, ~ IsInt falsev n.
Axiom watermelon_nonint : forall n, ~ IsInt watermelon n.
Axiom v42_isint : IsInt v42 n42.

Notation "42%Z" := n42.

Example test_case_mixed: filter_integers_spec [apple; real; nonev; falsev; watermelon; v42; real] [42%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  exact apple_nonint.
  eapply fir_cons_nonint.
  exact real_nonint.
  eapply fir_cons_nonint.
  exact nonev_nonint.
  eapply fir_cons_nonint.
  exact falsev_nonint.
  eapply fir_cons_nonint.
  exact watermelon_nonint.
  eapply fir_cons_int.
  exact v42_isint.
  eapply fir_cons_nonint.
  exact real_nonint.
  constructor.
Qed.