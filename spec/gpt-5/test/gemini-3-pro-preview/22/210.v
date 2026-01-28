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

Parameter v6 : Any.
Parameter v1 : Any.
Parameter v7 : Any.
Parameter vList : Any.
Parameter vNil : Any.

Axiom IsInt_v6 : IsInt v6 6%Z.
Axiom IsInt_v1 : IsInt v1 1%Z.
Axiom IsInt_v7 : IsInt v7 7%Z.
Axiom NotInt_vList : forall n, ~ IsInt vList n.
Axiom NotInt_vNil : forall n, ~ IsInt vNil n.

Example test_filter_integers : filter_integers_spec [v6; vList; v1; vNil; vNil; vList; v7; vNil] [6%Z; 1%Z; 7%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 6%Z).
  - apply IsInt_v6.
  - apply fir_cons_nonint.
    + apply NotInt_vList.
    + apply fir_cons_int with (n := 1%Z).
      * apply IsInt_v1.
      * apply fir_cons_nonint.
        -- apply NotInt_vNil.
        -- apply fir_cons_nonint.
           ++ apply NotInt_vNil.
           ++ apply fir_cons_nonint.
              ** apply NotInt_vList.
              ** apply fir_cons_int with (n := 7%Z).
                 --- apply IsInt_v7.
                 --- apply fir_cons_nonint.
                     +++ apply NotInt_vNil.
                     +++ apply fir_nil.
Qed.