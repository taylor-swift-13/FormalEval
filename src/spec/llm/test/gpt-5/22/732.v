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

Parameter dict1 : Any.
Parameter dict2 : Any.
Parameter dict3 : Any.
Parameter dict4 : Any.
Parameter dict5 : Any.
Parameter dict6 : Any.

Axiom dict1_nonint : forall n, ~ IsInt dict1 n.
Axiom dict2_nonint : forall n, ~ IsInt dict2 n.
Axiom dict3_nonint : forall n, ~ IsInt dict3 n.
Axiom dict4_nonint : forall n, ~ IsInt dict4 n.
Axiom dict5_nonint : forall n, ~ IsInt dict5 n.
Axiom dict6_nonint : forall n, ~ IsInt dict6 n.

Example test_case_new: filter_integers_spec [dict1; dict2; dict3; dict4; dict5; dict6] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - exact dict1_nonint.
  - eapply fir_cons_nonint.
    + exact dict2_nonint.
    + eapply fir_cons_nonint.
      * exact dict3_nonint.
      * eapply fir_cons_nonint.
        { exact dict4_nonint. }
        { eapply fir_cons_nonint.
          - exact dict5_nonint.
          - eapply fir_cons_nonint.
            + exact dict6_nonint.
            + apply fir_nil. }
Qed.