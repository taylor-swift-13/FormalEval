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

Example test_case_new :
  forall v1 v2 v3 v4 v5 v6 n1 n2 n3,
    IsInt v1 n1 ->
    (forall n, ~ IsInt v2 n) ->
    (forall n, ~ IsInt v3 n) ->
    (forall n, ~ IsInt v4 n) ->
    IsInt v5 n2 ->
    IsInt v6 n3 ->
    filter_integers_spec [v1; v2; v3; v4; v5; v6] [n1; n2; n3].
Proof.
  unfold filter_integers_spec.
  intros v1 v2 v3 v4 v5 v6 n1 n2 n3 H1 Hn2 Hn3 Hn4 H5 H6.
  apply (fir_cons_int v1 n1 [v2; v3; v4; v5; v6] [n2; n3]).
  - exact H1.
  - apply (fir_cons_nonint v2 [v3; v4; v5; v6] [n2; n3]).
    + exact Hn2.
    + apply (fir_cons_nonint v3 [v4; v5; v6] [n2; n3]).
      * exact Hn3.
      * apply (fir_cons_nonint v4 [v5; v6] [n2; n3]).
        { exact Hn4. }
        { apply (fir_cons_int v5 n2 [v6] [n3]).
          - exact H5.
          - apply (fir_cons_int v6 n3 [] []).
            + exact H6.
            + constructor.
        }
Qed.