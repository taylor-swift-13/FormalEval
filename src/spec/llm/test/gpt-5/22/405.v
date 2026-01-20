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

Parameter one four : int.
Notation "1%Z" := one.
Notation "4%Z" := four.

Parameters v1 v2 v3 v4 v5 v6 v7 v8 v9 : Any.
Axiom IsInt_v1 : IsInt v1 1%Z.
Axiom IsInt_v2 : IsInt v2 4%Z.
Axiom NonInt_v3 : forall n, ~ IsInt v3 n.
Axiom NonInt_v4 : forall n, ~ IsInt v4 n.
Axiom NonInt_v5 : forall n, ~ IsInt v5 n.
Axiom NonInt_v6 : forall n, ~ IsInt v6 n.
Axiom NonInt_v7 : forall n, ~ IsInt v7 n.
Axiom NonInt_v8 : forall n, ~ IsInt v8 n.
Axiom NonInt_v9 : forall n, ~ IsInt v9 n.

Example test_case_mixed: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9] [1%Z; 4%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (v := v1) (n := 1%Z) (vs := [v2; v3; v4; v5; v6; v7; v8; v9]) (res := [4%Z]).
  - exact IsInt_v1.
  - apply fir_cons_int with (v := v2) (n := 4%Z) (vs := [v3; v4; v5; v6; v7; v8; v9]) (res := []).
    + exact IsInt_v2.
    + apply fir_cons_nonint with (v := v3) (vs := [v4; v5; v6; v7; v8; v9]) (res := []).
      * exact NonInt_v3.
      * apply fir_cons_nonint with (v := v4) (vs := [v5; v6; v7; v8; v9]) (res := []).
        -- exact NonInt_v4.
        -- apply fir_cons_nonint with (v := v5) (vs := [v6; v7; v8; v9]) (res := []).
           ++ exact NonInt_v5.
           ++ apply fir_cons_nonint with (v := v6) (vs := [v7; v8; v9]) (res := []).
              ** exact NonInt_v6.
              ** apply fir_cons_nonint with (v := v7) (vs := [v8; v9]) (res := []).
                 --- exact NonInt_v7.
                 --- apply fir_cons_nonint with (v := v8) (vs := [v9]) (res := []).
                     **** exact NonInt_v8.
                     **** apply fir_cons_nonint with (v := v9) (vs := []) (res := []).
                          ++++ exact NonInt_v9.
                          ++++ constructor.
Qed.