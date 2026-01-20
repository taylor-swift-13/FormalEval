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

Parameters v1 v2 v3 v4 v5 v6 : Any.
Parameters n1 n4 n5 : int.
Axiom IsInt_v1 : IsInt v1 n1.
Axiom NonInt_v2 : forall n, ~ IsInt v2 n.
Axiom NonInt_v3 : forall n, ~ IsInt v3 n.
Axiom IsInt_v4 : IsInt v4 n4.
Axiom IsInt_v5 : IsInt v5 n5.
Axiom NonInt_v6 : forall n, ~ IsInt v6 n.

Example test_case_1: filter_integers_spec [v1; v2; v3; v4; v5; v6] [n1; n4; n5].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int with (v:=v1) (n:=n1).
  - apply IsInt_v1.
  - eapply fir_cons_nonint with (v:=v2).
    + apply NonInt_v2.
    + eapply fir_cons_nonint with (v:=v3).
      * apply NonInt_v3.
      * eapply fir_cons_int with (v:=v4) (n:=n4).
        -- apply IsInt_v4.
        -- eapply fir_cons_int with (v:=v5) (n:=n5).
           ++ apply IsInt_v5.
           ++ eapply fir_cons_nonint with (v:=v6).
              ** apply NonInt_v6.
              ** apply fir_nil.
Qed.