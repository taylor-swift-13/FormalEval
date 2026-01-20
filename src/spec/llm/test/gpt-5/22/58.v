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
Parameter how : Any.
Parameter world : Any.
Parameter habcow : Any.
Parameter te : Any.

Axiom hello_nonint : forall n, ~ IsInt hello n.
Axiom how_nonint : forall n, ~ IsInt how n.
Axiom world_nonint : forall n, ~ IsInt world n.
Axiom habcow_nonint : forall n, ~ IsInt habcow n.
Axiom te_nonint : forall n, ~ IsInt te n.

Example test_case_strings: filter_integers_spec [hello; how; world; habcow; te] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint. exact hello_nonint.
  eapply fir_cons_nonint. exact how_nonint.
  eapply fir_cons_nonint. exact world_nonint.
  eapply fir_cons_nonint. exact habcow_nonint.
  eapply fir_cons_nonint. exact te_nonint.
  constructor.
Qed.