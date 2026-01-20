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

Parameter hello worldd how heho_2wllhelloo are you hellhelloo : Any.

Axiom hello_nonint : forall n, ~ IsInt hello n.
Axiom worldd_nonint : forall n, ~ IsInt worldd n.
Axiom how_nonint : forall n, ~ IsInt how n.
Axiom heho_2wllhelloo_nonint : forall n, ~ IsInt heho_2wllhelloo n.
Axiom are_nonint : forall n, ~ IsInt are n.
Axiom you_nonint : forall n, ~ IsInt you n.
Axiom hellhelloo_nonint : forall n, ~ IsInt hellhelloo n.

Example test_case_strings:
  filter_integers_spec [hello; worldd; how; heho_2wllhelloo; are; you; hellhelloo; how; you] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint. exact hello_nonint.
  eapply fir_cons_nonint. exact worldd_nonint.
  eapply fir_cons_nonint. exact how_nonint.
  eapply fir_cons_nonint. exact heho_2wllhelloo_nonint.
  eapply fir_cons_nonint. exact are_nonint.
  eapply fir_cons_nonint. exact you_nonint.
  eapply fir_cons_nonint. exact hellhelloo_nonint.
  eapply fir_cons_nonint. exact how_nonint.
  eapply fir_cons_nonint. exact you_nonint.
  constructor.
Qed.