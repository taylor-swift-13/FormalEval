Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
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

Parameter complex_value : Any.
Axiom complex_value_is_int : IsInt complex_value 1%Z.

Example test_case_mixed: filter_integers_spec [complex_value] [1%Z].
Proof.
  unfold filter_integers_spec.
  apply (fir_cons_int complex_value 1%Z [] []).
  - exact complex_value_is_int.
  - apply fir_nil.
Qed.