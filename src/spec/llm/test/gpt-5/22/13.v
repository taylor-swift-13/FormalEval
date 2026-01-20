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

Parameter hello world how are you : Any.
Axiom nonint_hello : forall n, ~ IsInt hello n.
Axiom nonint_world : forall n, ~ IsInt world n.
Axiom nonint_how : forall n, ~ IsInt how n.
Axiom nonint_are : forall n, ~ IsInt are n.
Axiom nonint_you : forall n, ~ IsInt you n.

Example test_case_strings: filter_integers_spec [hello; world; how; are; you] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - exact nonint_hello.
  - eapply fir_cons_nonint.
    + exact nonint_world.
    + eapply fir_cons_nonint.
      * exact nonint_how.
      * eapply fir_cons_nonint.
        { exact nonint_are. }
        { eapply fir_cons_nonint.
          - exact nonint_you.
          - constructor. }
Qed.