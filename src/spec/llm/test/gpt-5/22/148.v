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

Parameters v1 v2 v3 v4 v5 v6 v7 v8 v9 : Any.
Parameters n1 n2 n3 n6 : int.
Axiom H1 : IsInt v1 n1.
Axiom H2 : IsInt v2 n2.
Axiom H3 : IsInt v3 n3.
Axiom H4_non : forall n, ~ IsInt v4 n.
Axiom H5_non : forall n, ~ IsInt v5 n.
Axiom H6 : IsInt v6 n6.
Axiom H7_non : forall n, ~ IsInt v7 n.
Axiom H8_non : forall n, ~ IsInt v8 n.
Axiom H9_non : forall n, ~ IsInt v9 n.

Example test_case_mixed:
  filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8; v9] [n1; n2; n3; n6].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int with (n := n1).
  - apply H1.
  - eapply fir_cons_int with (n := n2).
    + apply H2.
    + eapply fir_cons_int with (n := n3).
      * apply H3.
      * eapply fir_cons_nonint.
        { exact H4_non. }
        { eapply fir_cons_nonint.
          { exact H5_non. }
          { eapply fir_cons_int with (n := n6).
            { apply H6. }
            { eapply fir_cons_nonint.
              { exact H7_non. }
              { eapply fir_cons_nonint.
                { exact H8_non. }
                { eapply fir_cons_nonint.
                  { exact H9_non. }
                  { apply fir_nil. } } } } } }
Qed.