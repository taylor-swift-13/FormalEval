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

Parameters v1 v2 v3 v4 : Any.
Parameter one_int : int.
Notation "1%Z" := one_int.
Parameter IsInt_v1 : IsInt v1 1%Z.
Parameter nonint_v2 : forall n, ~ IsInt v2 n.
Parameter nonint_v3 : forall n, ~ IsInt v3 n.
Parameter nonint_v4 : forall n, ~ IsInt v4 n.

Example test_case_new: filter_integers_spec [v1; v2; v3; v4] [1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact IsInt_v1|].
  eapply fir_cons_nonint; [exact nonint_v2|].
  eapply fir_cons_nonint; [exact nonint_v3|].
  eapply fir_cons_nonint; [exact nonint_v4|].
  constructor.
Qed.