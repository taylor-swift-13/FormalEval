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

Parameter v1 v2 v3 v4 v5 v6 v7 v8 : Any.
Parameter one : int.
Parameter H1 : IsInt v1 one.
Parameter H8 : IsInt v8 one.
Parameter Hn2 : forall n, ~ IsInt v2 n.
Parameter Hn3 : forall n, ~ IsInt v3 n.
Parameter Hn4 : forall n, ~ IsInt v4 n.
Parameter Hn5 : forall n, ~ IsInt v5 n.
Parameter Hn6 : forall n, ~ IsInt v6 n.
Parameter Hn7 : forall n, ~ IsInt v7 n.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4; v5; v6; v7; v8] [one; one].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int.
  - exact H1.
  - eapply fir_cons_nonint.
    + exact Hn2.
    + eapply fir_cons_nonint.
      * exact Hn3.
      * eapply fir_cons_nonint.
        { exact Hn4. }
        eapply fir_cons_nonint.
        { exact Hn5. }
        eapply fir_cons_nonint.
        { exact Hn6. }
        eapply fir_cons_nonint.
        { exact Hn7. }
        eapply fir_cons_int.
        { exact H8. }
        constructor.
Qed.