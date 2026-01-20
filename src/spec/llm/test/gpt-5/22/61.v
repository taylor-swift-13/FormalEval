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

Parameter hello how world empty_string ho2w worldhow test you : Any.
Axiom NonInt_hello : forall n, ~ IsInt hello n.
Axiom NonInt_how : forall n, ~ IsInt how n.
Axiom NonInt_world : forall n, ~ IsInt world n.
Axiom NonInt_empty_string : forall n, ~ IsInt empty_string n.
Axiom NonInt_ho2w : forall n, ~ IsInt ho2w n.
Axiom NonInt_worldhow : forall n, ~ IsInt worldhow n.
Axiom NonInt_test : forall n, ~ IsInt test n.
Axiom NonInt_you : forall n, ~ IsInt you n.

Example test_case_strings: filter_integers_spec [hello; how; world; empty_string; ho2w; worldhow; test; you] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint.
  - apply NonInt_hello.
  - eapply fir_cons_nonint.
    + apply NonInt_how.
    + eapply fir_cons_nonint.
      * apply NonInt_world.
      * eapply fir_cons_nonint.
        -- apply NonInt_empty_string.
        -- eapply fir_cons_nonint.
           ++ apply NonInt_ho2w.
           ++ eapply fir_cons_nonint.
              ** apply NonInt_worldhow.
              ** eapply fir_cons_nonint.
                 --- apply NonInt_test.
                 --- eapply fir_cons_nonint.
                     ---- apply NonInt_you.
                     ---- apply fir_nil.
Qed.