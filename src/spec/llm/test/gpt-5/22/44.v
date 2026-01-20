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

Parameter hello : Any.
Parameter worldd : Any.
Parameter how : Any.
Parameter heho_2wllhelloo : Any.
Parameter are : Any.
Parameter you : Any.
Parameter hellhelloo : Any.

Axiom nonint_hello : forall n, ~ IsInt hello n.
Axiom nonint_worldd : forall n, ~ IsInt worldd n.
Axiom nonint_how : forall n, ~ IsInt how n.
Axiom nonint_heho_2wllhelloo : forall n, ~ IsInt heho_2wllhelloo n.
Axiom nonint_are : forall n, ~ IsInt are n.
Axiom nonint_you : forall n, ~ IsInt you n.
Axiom nonint_hellhelloo : forall n, ~ IsInt hellhelloo n.

Example test_case_strings: filter_integers_spec [hello; worldd; how; heho_2wllhelloo; are; you; hellhelloo; how] [].
Proof.
  unfold filter_integers_spec.
  apply (fir_cons_nonint hello); [apply nonint_hello |].
  apply (fir_cons_nonint worldd); [apply nonint_worldd |].
  apply (fir_cons_nonint how); [apply nonint_how |].
  apply (fir_cons_nonint heho_2wllhelloo); [apply nonint_heho_2wllhelloo |].
  apply (fir_cons_nonint are); [apply nonint_are |].
  apply (fir_cons_nonint you); [apply nonint_you |].
  apply (fir_cons_nonint hellhelloo); [apply nonint_hellhelloo |].
  apply (fir_cons_nonint how); [apply nonint_how |].
  constructor.
Qed.