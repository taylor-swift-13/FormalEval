Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

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

Parameter val1 : Any.
Parameter val2 : Any.
Parameter val3 : Any.
Parameter val4 : Any.
Parameter val5 : Any.
Parameter val6 : Any.
Parameter val7 : Any.
Parameter val8 : Any.
Parameter val9 : Any.

Axiom val1_not_int : forall n, ~ IsInt val1 n.
Axiom val2_is_int : IsInt val2 2.
Axiom val3_is_int : IsInt val3 0.
Axiom val4_not_int : forall n, ~ IsInt val4 n.
Axiom val5_not_int : forall n, ~ IsInt val5 n.
Axiom val6_not_int : forall n, ~ IsInt val6 n.
Axiom val7_not_int : forall n, ~ IsInt val7 n.
Axiom val8_not_int : forall n, ~ IsInt val8 n.
Axiom val9_is_int : IsInt val9 1.

Example test_filter_integers_complex : filter_integers_spec [val1; val2; val3; val4; val5; val6; val7; val8; val9] [2; 0; 1].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_nonint. apply val1_not_int.
  apply fir_cons_int with (n := 2). apply val2_is_int.
  apply fir_cons_int with (n := 0). apply val3_is_int.
  apply fir_cons_nonint. apply val4_not_int.
  apply fir_cons_nonint. apply val5_not_int.
  apply fir_cons_nonint. apply val6_not_int.
  apply fir_cons_nonint. apply val7_not_int.
  apply fir_cons_nonint. apply val8_not_int.
  apply fir_cons_int with (n := 1). apply val9_is_int.
  apply fir_nil.
Qed.