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

Parameter val_mixed_1 : Any.
Parameter val_7 : Any.
Parameter val_mixed_2 : Any.
Parameter int_7 : int.

Axiom val_mixed_1_not_int : forall n, ~ IsInt val_mixed_1 n.
Axiom val_7_is_int : IsInt val_7 int_7.
Axiom val_mixed_2_not_int : forall n, ~ IsInt val_mixed_2 n.

Example test_filter_integers_complex : filter_integers_spec [val_mixed_1; val_7; val_mixed_2] [int_7].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint.
  - apply val_mixed_1_not_int.
  - apply fir_cons_int with (n := int_7).
    + apply val_7_is_int.
    + apply fir_cons_nonint.
      * apply val_mixed_2_not_int.
      * apply fir_nil.
Qed.