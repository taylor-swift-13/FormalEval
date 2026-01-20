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

Parameter v2 v1 vone vlist vdict : Any.
Parameter z2 z1 : int.
Notation "2%Z" := z2.
Notation "1%Z" := z1.
Axiom IsInt_v2 : IsInt v2 2%Z.
Axiom IsInt_v1 : IsInt v1 1%Z.
Axiom NonInt_vone : forall n, ~ IsInt vone n.
Axiom NonInt_vlist : forall n, ~ IsInt vlist n.
Axiom NonInt_vdict : forall n, ~ IsInt vdict n.

Example test_case_mixed: filter_integers_spec [v2; v1; vone; vlist; vdict] [2%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 2%Z).
  - exact IsInt_v2.
  - apply fir_cons_int with (n := 1%Z).
    + exact IsInt_v1.
    + apply fir_cons_nonint.
      * exact NonInt_vone.
      * apply fir_cons_nonint.
        { exact NonInt_vlist. }
        { apply fir_cons_nonint.
          { exact NonInt_vdict. }
          { constructor. } }
Qed.