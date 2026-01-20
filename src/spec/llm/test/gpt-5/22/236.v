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

Parameter v6 l23 : Any.
Parameter six : int.
Axiom IsInt_v6_six : IsInt v6 six.
Axiom l23_nonint : forall n, ~ IsInt l23 n.

Example test_case_nested: filter_integers_spec [v6; l23] [six].
Proof.
  unfold filter_integers_spec.
  apply (fir_cons_int v6 six [l23] []).
  - exact IsInt_v6_six.
  - apply (fir_cons_nonint l23 [] []).
    + exact l23_nonint.
    + constructor.
Qed.