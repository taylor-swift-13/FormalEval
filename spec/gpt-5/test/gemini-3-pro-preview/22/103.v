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

Parameter val1 val2 val3 val4 val5 val6 : Any.
Parameter int1 : int.

Axiom val1_is_int : IsInt val1 int1.
Axiom val2_not_int : forall n, ~ IsInt val2 n.
Axiom val3_not_int : forall n, ~ IsInt val3 n.
Axiom val4_not_int : forall n, ~ IsInt val4 n.
Axiom val5_not_int : forall n, ~ IsInt val5 n.
Axiom val6_not_int : forall n, ~ IsInt val6 n.

Example test_filter_integers_mixed : 
  filter_integers_spec [val1; val2; val3; val4; val5; val6] [int1].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int.
  - apply val1_is_int.
  - apply fir_cons_nonint.
    + apply val2_not_int.
    + apply fir_cons_nonint.
      * apply val3_not_int.
      * apply fir_cons_nonint.
        -- apply val4_not_int.
        -- apply fir_cons_nonint.
           ++ apply val5_not_int.
           ++ apply fir_cons_nonint.
              ** apply val6_not_int.
              ** apply fir_nil.
Qed.