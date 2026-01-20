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

Parameters a0 a1 a2 a3 a4 : Any.
Axiom a0_is_int : IsInt a0 0%Z.
Axiom a1_nonint : forall n, ~ IsInt a1 n.
Axiom a2_nonint : forall n, ~ IsInt a2 n.
Axiom a3_nonint : forall n, ~ IsInt a3 n.
Axiom a4_nonint : forall n, ~ IsInt a4 n.

Example test_case_mixed: filter_integers_spec [a0; a1; a2; a3; a4] [0%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (v := a0) (n := 0%Z) (vs := [a1; a2; a3; a4]) (res := []).
  - apply a0_is_int.
  - apply fir_cons_nonint with (v := a1) (vs := [a2; a3; a4]) (res := []).
    + intros n; apply a1_nonint.
    + apply fir_cons_nonint with (v := a2) (vs := [a3; a4]) (res := []).
      * intros n; apply a2_nonint.
      * apply fir_cons_nonint with (v := a3) (vs := [a4]) (res := []).
        -- intros n; apply a3_nonint.
        -- apply fir_cons_nonint with (v := a4) (vs := []) (res := []).
           ++ intros n; apply a4_nonint.
           ++ constructor.
Qed.