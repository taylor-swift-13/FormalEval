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
Parameter test : Any.
Parameter you : Any.

Axiom hello_not_int : forall n, ~ IsInt hello n.
Axiom how_not_int : forall n, ~ IsInt how n.
Axiom world_not_int : forall n, ~ IsInt world n.
Axiom test_not_int : forall n, ~ IsInt test n.
Axiom you_not_int : forall n, ~ IsInt you n.

Example test_case_strings: filter_integers_spec [hello; how; world; how; test; you] [].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply hello_not_int |].
  eapply fir_cons_nonint; [apply how_not_int |].
  eapply fir_cons_nonint; [apply world_not_int |].
  eapply fir_cons_nonint; [apply how_not_int |].
  eapply fir_cons_nonint; [apply test_not_int |].
  eapply fir_cons_nonint; [apply you_not_int |].
  constructor.
Qed.