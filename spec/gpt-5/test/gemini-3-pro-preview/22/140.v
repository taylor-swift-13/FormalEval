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

Parameter v1 : Any.
Parameter v2 : Any.
Parameter v3 : Any.

Axiom v1_not_int : forall n, ~ IsInt v1 n.
Axiom v2_not_int : forall n, ~ IsInt v2 n.
Axiom v3_is_int : IsInt v3 7%Z.

Example test_filter_integers_mixed : filter_integers_spec [v1; v2; v3] [7%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint.
  - apply v1_not_int.
  - apply fir_cons_nonint.
    + apply v2_not_int.
    + apply fir_cons_int with (n := 7%Z).
      * apply v3_is_int.
      * apply fir_nil.
Qed.