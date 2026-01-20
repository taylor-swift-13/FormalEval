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

Parameters v1 v2 v3 v4 : Any.
Parameters n1 n8 n9a n9b : int.
Axiom H1 : IsInt v1 n1.
Axiom H2 : IsInt v2 n8.
Axiom H3 : IsInt v3 n9a.
Axiom H4 : IsInt v4 n9b.

Example test_case: filter_integers_spec [v1; v2; v3; v4] [n1; n8; n9a; n9b].
Proof.
  unfold filter_integers_spec.
  econstructor; [apply H1|].
  econstructor; [apply H2|].
  econstructor; [apply H3|].
  econstructor; [apply H4|].
  constructor.
Qed.