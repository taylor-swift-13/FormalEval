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

Parameter v1 v2 v3 v4 v5 : Any.
Parameter z1 z29 : int.
Notation "1%Z" := z1.
Notation "29%Z" := z29.

Axiom IsInt_v1 : IsInt v1 1%Z.
Axiom IsInt_v3 : IsInt v3 29%Z.
Axiom NonInt_v2 : forall n, ~ IsInt v2 n.
Axiom NonInt_v4 : forall n, ~ IsInt v4 n.
Axiom NonInt_v5 : forall n, ~ IsInt v5 n.

Example test_case_mixed: filter_integers_spec [v1; v2; v3; v4; v5] [1%Z; 29%Z].
Proof.
  unfold filter_integers_spec.
  apply (fir_cons_int v1 1%Z [v2; v3; v4; v5] [29%Z]).
  - exact IsInt_v1.
  - apply (fir_cons_nonint v2 [v3; v4; v5] [29%Z]).
    + intros n; apply NonInt_v2.
    + apply (fir_cons_int v3 29%Z [v4; v5] []).
      * exact IsInt_v3.
      * apply (fir_cons_nonint v4 [v5] []).
        { intros n; apply NonInt_v4. }
        apply (fir_cons_nonint v5 [] []).
        { intros n; apply NonInt_v5. }
        constructor.
Qed.