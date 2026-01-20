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

Parameter a1 a2 a3 a4 a5 : Any.
Parameter z1 : int.
Notation "1%Z" := z1.
Axiom Ha1 : IsInt a1 1%Z.
Axiom Hna2 : forall n, ~ IsInt a2 n.
Axiom Hna3 : forall n, ~ IsInt a3 n.
Axiom Hna4 : forall n, ~ IsInt a4 n.
Axiom Hna5 : forall n, ~ IsInt a5 n.

Example test_case_new: filter_integers_spec [a1; a2; a3; a4; a5] [1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact Ha1|].
  eapply fir_cons_nonint; [exact Hna2|].
  eapply fir_cons_nonint; [exact Hna3|].
  eapply fir_cons_nonint; [exact Hna4|].
  eapply fir_cons_nonint; [exact Hna5|].
  constructor.
Qed.