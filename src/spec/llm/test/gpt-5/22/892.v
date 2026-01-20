Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

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

Parameters v1 v2 v3 v4 v5 v6 v7 v8 : Any.
Axiom v1_is_int : IsInt v1 1%Z.
Axiom v2_not_int : forall n, ~ IsInt v2 n.
Axiom v3_not_int : forall n, ~ IsInt v3 n.
Axiom v4_not_int : forall n, ~ IsInt v4 n.
Axiom v5_not_int : forall n, ~ IsInt v5 n.
Axiom v6_not_int : forall n, ~ IsInt v6 n.
Axiom v7_not_int : forall n, ~ IsInt v7 n.
Axiom v8_not_int : forall n, ~ IsInt v8 n.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8] [1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int with (v:=v1) (n:=1%Z).
  - apply v1_is_int.
  - eapply fir_cons_nonint with (v:=v2).
    + apply v2_not_int.
    + eapply fir_cons_nonint with (v:=v3).
      * apply v3_not_int.
      * eapply fir_cons_nonint with (v:=v4).
        -- apply v4_not_int.
        -- eapply fir_cons_nonint with (v:=v5).
           ++ apply v5_not_int.
           ++ eapply fir_cons_nonint with (v:=v6).
              ** apply v6_not_int.
              ** eapply fir_cons_nonint with (v:=v7).
                 *** apply v7_not_int.
                 *** eapply fir_cons_nonint with (v:=v8).
                     **** apply v8_not_int.
                     **** constructor.
Qed.